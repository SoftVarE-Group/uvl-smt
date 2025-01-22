package conversion;

import de.vill.model.Feature;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Encodes Boolean cardinality constraints using the method proposed by Carsten Sinz in "Towards an Optimal CNF Encoding of Boolean Cardinality Constraints"
 * Idea is to count the variables using a sequential counter and then check for a violation with overflow variables
 * At least and at most is then realized with at most positive and at most negative
 * Refactor duality for at least and at most, seems error-prone
 *
 * @author Chico Sundermann
 */
public class CardinalityConverter {

    List<String> originalVariables; // Variables that are part of the original formula and restricted by the cardinality
    BooleanFormulaManager formulaManager;

    int lower;
    int upper;
    int currentBound;
    boolean atMost;

    String suffix;

    public CardinalityConverter(int lower, int upper, List<Feature> originalFeatures, BooleanFormulaManager formulaManager) {
        this.originalVariables = originalFeatures.stream().map(Feature::getIdentifier).collect(Collectors.toList());
        this.formulaManager = formulaManager;
        this.lower = lower;
        this.upper = upper;
    }

    public CardinalityConverter(List<String> originalVariables, int lower, int upper, BooleanFormulaManager formulaManager) {
        this.originalVariables = originalVariables;
        this.lower = lower;
        this.upper = upper;
        this.formulaManager = formulaManager;
    }

    public BooleanFormula convertCardinality() {
        List<BooleanFormula> formulas = new ArrayList<>();
        if (upper == 0) { // all variables are dead
            for (String originalVariable : originalVariables) {
                formulas.add(formulaManager.not(formulaManager.makeVariable(originalVariable)));
            }
            return formulaManager.and(formulas);
        } else {
            BooleanFormula atMost = createAtmostk();
            BooleanFormula atLeast = createAtLeastk();
            return formulaManager.and(atMost, atLeast);
        }
    }

    public BooleanFormula createAtmostk() {
        this.atMost = true;
        this.currentBound = upper;
        this.suffix = "-upper";

        return buildConstraints();
    }

    public BooleanFormula createAtLeastk() {
        this.atMost = false;
        this.currentBound = originalVariables.size() - lower;
        this.suffix = "-lower";

        return buildConstraints();
    }

    private BooleanFormula buildConstraints() {
        List<BooleanFormula> highLevelConstraints = new ArrayList<>();
        // Initialize counter constraints
        for (int i = 0; i < originalVariables.size(); i++) {
            highLevelConstraints.add(createCounterConstraints(i));
        }
        // Initialize overflow variable constraints
        highLevelConstraints.add(createOverflowAggregate());
        highLevelConstraints.add(createOverflowConstraints());

        return formulaManager.and(highLevelConstraints);
    }


    private BooleanFormula createOverflowVariable(String originalVariable) {
        return formulaManager.makeVariable(originalVariable + suffix + "_overflow");
    }

    private BooleanFormula createCounterConstraints(int currentIndex) {
        BooleanFormula originalLiteral = getOriginalVariable(currentIndex);
        List<BooleanFormula> upperCounterConstraints = new ArrayList<>();
        if (currentIndex == 0) {
            upperCounterConstraints.add(formulaManager.equivalence(originalLiteral, createCounterLiteral(currentIndex, 0))); // s_0,0 <=> x_0
            for (int j = 1; j < this.currentBound; j++) {
                upperCounterConstraints.add(formulaManager.not(createCounterLiteral(currentIndex, j))); // s_0,j <=> false
            }
        } else {
            upperCounterConstraints.add(formulaManager.equivalence(formulaManager.or(originalLiteral, createCounterLiteral(currentIndex - 1, 0)), createCounterLiteral(currentIndex, 0)));
            for (int j = 1; j < this.currentBound; j++) {
                upperCounterConstraints.add(
                        formulaManager.equivalence(
                                createCounterLiteral(currentIndex, j),
                                formulaManager.or(
                                        formulaManager.and(
                                                originalLiteral,
                                                createCounterLiteral(currentIndex - 1, j - 1)
                                        ),
                                        createCounterLiteral(currentIndex - 1, j)
                                )
                        )); // s_i,j <=> x_i & s_i-1,j-1 v s_i-1,j
            }
        }
        return formulaManager.and(upperCounterConstraints);
    }

    private BooleanFormula getOriginalVariable(int variableIndex) {
        if (atMost) {
            return formulaManager.makeVariable(originalVariables.get(variableIndex));
        } else {
            return formulaManager.not(formulaManager.makeVariable(originalVariables.get(variableIndex)));
        }
    }

    private BooleanFormula createCounterLiteral(int variableIndex, int counterIndex) {
        return formulaManager.makeVariable(originalVariables.get(variableIndex) + suffix + "_" + variableIndex + "_" + counterIndex);
    }

    private BooleanFormula createOverflowConstraints() {
        List<BooleanFormula> overflowConstraints = new ArrayList<>();
        for (int i = 1; i < originalVariables.size(); i++) { // v_0 is always false (no overflow) except when having a cardinality upper of 0, which is handled separately
            overflowConstraints.add(formulaManager.equivalence(
                    createOverflowVariable(originalVariables.get(i)),
                    formulaManager.and(getOriginalVariable(i), createCounterLiteral(i - 1, currentBound - 1)))); // v_i <=> x_i & s_i-1,k
        }
        return formulaManager.and(overflowConstraints);
    }

    private BooleanFormula createOverflowAggregate() {
        List<BooleanFormula> literals = new ArrayList<>();
        for (String variable : originalVariables) {
            literals.add(formulaManager.not(createOverflowVariable(variable)));
        }
        return formulaManager.and(literals);
    }


}
