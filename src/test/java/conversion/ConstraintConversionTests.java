package conversion;


import Reasoning.SMTSatisfiabilityChecker;
import de.vill.main.UVLModelFactory;
import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import de.vill.model.Group;
import de.vill.model.constraint.Constraint;
import de.vill.model.constraint.EqualEquationConstraint;
import de.vill.model.expression.*;
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

import java.nio.file.Paths;
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

    @Test
    void testSimpleGroups() throws InvalidConfigurationException {
        BooleanFormula or = buildGroup(booleanVariables, Group.GroupType.OR);
        BooleanFormula optional = buildGroup(booleanVariables, Group.GroupType.OPTIONAL);
        BooleanFormula mandatory = buildGroup(booleanVariables, Group.GroupType.MANDATORY);

        BooleanFormula parentLiteral = booleanManager.makeVariable(PARENT);

        BooleanFormula assignment1n2 = buildSimpleAssignment(booleanVariables, 1, 2);
        BooleanFormula assignment5n0 = buildSimpleAssignment(booleanVariables, 5, 0);
        BooleanFormula assignment0n5 = buildSimpleAssignment(booleanVariables, 0, 5);

        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(or, parentLiteral, assignment1n2), context);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(or, parentLiteral, assignment5n0), context);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(or, parentLiteral, assignment0n5), context);

        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(optional, parentLiteral, assignment1n2), context);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(optional, parentLiteral, assignment5n0), context);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(optional, parentLiteral, assignment0n5), context);

        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(mandatory, parentLiteral, assignment1n2), context);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(mandatory, parentLiteral, assignment5n0), context);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(mandatory, parentLiteral, assignment0n5), context);
    }


    @Test
    void testArithmeticEqualities() throws InvalidConfigurationException {
        UVLModelFactory factory = new UVLModelFactory();
        FeatureModel attributedBase = factory.parse(Paths.get("src/test/resources/arithmetic/attributedbase.uvl"));

        FmToSMTConverter converter = new FmToSMTConverter(context, attributedBase);
        SMTSatisfiabilityChecker checker = new SMTSatisfiabilityChecker(converter.convertFeatureModel(), context);


        Expression alternativeFeature1 = getPrice(attributedBase, "AlternativeOne");
        Expression alternativeFeature2 = getPrice(attributedBase, "AlternativeTwo");

        Expression orFeature1 = getPrice(attributedBase, "OrOne");
        Expression orFeature2 = getPrice(attributedBase, "OrTwo");

        Expression optionalFeature1 = getPrice(attributedBase, "OptionalOne");
        Expression optionalFeature2 = getPrice(attributedBase, "OptionalTwo");

        Expression mandatoryFeature1 = getPrice(attributedBase, "MandatoryOne");
        Expression mandatoryFeature2 = getPrice(attributedBase, "MandatoryTwo");

        // Addition

        // SAT(att1 + att2 = 30) with att1 = 20 and att2 = 10 in alternative
        Constraint simpleAddUnsat = new EqualEquationConstraint(new AddExpression(alternativeFeature1, alternativeFeature2), new NumberExpression(30));
        assert !checker.isSatWith(converter.convertConstraintToSMT(simpleAddUnsat));

        // SAT(att1 + att2 = 20) with att1 = 20 and att2 = 10 in alternative
        Constraint simpleAddSat = new EqualEquationConstraint(new AddExpression(alternativeFeature1, alternativeFeature2), new NumberExpression(20));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleAddSat));

        // Multiplication

        Constraint simpleMultSat = new EqualEquationConstraint(new MulExpression(orFeature1, orFeature2), new NumberExpression(0));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleMultSat));

        Constraint simpleMultSat2 = new EqualEquationConstraint(new MulExpression(orFeature1, orFeature2), new NumberExpression(6));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleMultSat2));

        Constraint simpleMultUnsat = new EqualEquationConstraint(new MulExpression(orFeature1, orFeature2), new NumberExpression(3));
        assert !checker.isSatWith(converter.convertConstraintToSMT(simpleMultUnsat));


        // Subtract

        Constraint simpleSubSat = new EqualEquationConstraint(new SubExpression(optionalFeature1, optionalFeature2), new NumberExpression(6));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleSubSat));

        Constraint simpleSubSat2 = new EqualEquationConstraint(new SubExpression(optionalFeature2, optionalFeature1), new NumberExpression(1));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleSubSat2));

        Constraint simpleSubUnsat = new EqualEquationConstraint(new SubExpression(optionalFeature1, optionalFeature2), new NumberExpression(3));
        assert !checker.isSatWith(converter.convertConstraintToSMT(simpleSubUnsat));

        // Divide
        Constraint simpleDivSat = new EqualEquationConstraint(new DivExpression(mandatoryFeature1, mandatoryFeature2), new NumberExpression(0));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleDivSat));

        Constraint simpleDivSat2 = new EqualEquationConstraint(new DivExpression(optionalFeature1, optionalFeature2), new NumberExpression(1));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleDivSat2));

        Constraint simpleDivUnknown = new EqualEquationConstraint(new DivExpression(alternativeFeature1, alternativeFeature2), new NumberExpression(100));
        assert checker.isSatWith(converter.convertConstraintToSMT(simpleDivUnknown));
    }

    private static Expression getPrice(FeatureModel model, String featureName) {
        return new LiteralExpression(model.getFeatureMap().get(featureName).getAttributes().get("Price"));
    }



    // Helper

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
