package conversion;


import Reasoning.SMTSatisfiabilityChecker;
import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import de.vill.model.Group;
import org.junit.jupiter.api.BeforeEach;
import org.junit.jupiter.api.Test;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.BooleanFormula;
import org.sosy_lab.java_smt.api.BooleanFormulaManager;
import org.sosy_lab.java_smt.api.SolverContext;

import java.util.ArrayList;
import java.util.List;

class ConstraintConversionTests {

    SolverContext context;

    BooleanFormulaManager booleanManager;

    List<String> booleanVariables;
    final static String PARENT = "p";

    FeatureModel emptyFeatureModel;

    @BeforeEach
    void setup() throws InvalidConfigurationException {
        this.context = SolverContextFactory.createSolverContext(Configuration.defaultConfiguration(), LogManager.createNullLogManager(), ShutdownManager.create().getNotifier(), SolverContextFactory.Solvers.Z3);
        this.booleanManager = context.getFormulaManager().getBooleanFormulaManager();

        booleanVariables = new ArrayList<>();
        booleanVariables.add("a");
        booleanVariables.add("b");
        booleanVariables.add("c");
        booleanVariables.add("d");
        booleanVariables.add("e");

        emptyFeatureModel = new FeatureModel();
    }
    @Test
    void testCardinalities() {


        BooleanFormula cardinality23 = buildCardinality(booleanVariables, 2 , 3);

        // [2,3] & 2 selected == SAT
        BooleanFormula satAssignment11 = buildSimpleAssignment(booleanVariables, 2, 3);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, satAssignment11), context);

        // [2,3] & 3 selected == SAT
        BooleanFormula satAssignment12 = buildSimpleAssignment(booleanVariables, 3, 1);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, satAssignment12), context);

        // [2,3] & 4 selected == !SAT
        BooleanFormula unsatAssignment11 = buildSimpleAssignment(booleanVariables, 4, 1);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, unsatAssignment11), context);

        // [2,3] & 4 deselected == !SAT
        BooleanFormula unsatAssignment12 = buildSimpleAssignment(booleanVariables, 1, 4);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, unsatAssignment12), context);


        BooleanFormula cardinality14 = buildCardinality(booleanVariables, 1, 4);

        // [1,4] & 1 selected == SAT
        BooleanFormula satAssignment21 = buildSimpleAssignment(booleanVariables, 1, 4);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment21), context);

        // [1,4] & 3 selected == SAT
        BooleanFormula satAssignment22 = buildSimpleAssignment(booleanVariables, 3, 0);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment22), context);

        // [1,4] & 5 selected == !SAT
        BooleanFormula unsatAssignment21 = buildSimpleAssignment(booleanVariables, 5, 0);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment21), context);

        // [1,4] & 5 deselected == !SAT
        BooleanFormula unsatAssignment22 = buildSimpleAssignment(booleanVariables, 0, 5);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment22), context);
    }

    @Test
    void testAlternative() throws InvalidConfigurationException {
        BooleanFormula alternative = buildGroup(booleanVariables, Group.GroupType.ALTERNATIVE);
        BooleanFormula parentLiteral = booleanManager.makeVariable(PARENT);

        BooleanFormula satAssignment = buildSimpleAssignment(booleanVariables, 1, 2);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(alternative, parentLiteral, satAssignment), context);

        BooleanFormula unsatAssignment = buildSimpleAssignment(booleanVariables, 2, 0);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(alternative, parentLiteral, unsatAssignment), context);

        BooleanFormula unsatAssignment2 = buildSimpleAssignment(booleanVariables, 0, 5);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(alternative, parentLiteral, unsatAssignment2), context);
    }

    private BooleanFormula buildCardinality(List<String> variables, int lower, int upper) {
        CardinalityConverter converter = new CardinalityConverter(variables, lower, upper, booleanManager);
        return converter.convertCardinality();
    }

    private BooleanFormula buildGroup(List<String> variables, Group.GroupType type) throws InvalidConfigurationException {
        FmToSMTConverter converter = new FmToSMTConverter(context, emptyFeatureModel);
        Feature parentFeature = new Feature(PARENT);
        Group alternative = new Group(type);
        alternative.setParentFeature(parentFeature);
        for (String variable : variables) {
            alternative.getFeatures().add(new Feature(variable));
        }
        return converter.convertGroup(alternative);
    }

    private BooleanFormula buildSimpleAssignment(List<String> variables, int numberSelected, int numberDeselected) {
        assert numberSelected + numberDeselected <= variables.size();
        List<BooleanFormula> assignments = new ArrayList<>();
        for (int i = 0; i < numberSelected; i++) {
            assignments.add(booleanManager.makeVariable(variables.get(i)));
        }
        for (int i = numberSelected; i < numberSelected + numberDeselected; i++) {
            assignments.add(booleanManager.not(booleanManager.makeVariable(variables.get(i))));
        }
        return booleanManager.and(assignments);
    }

}
