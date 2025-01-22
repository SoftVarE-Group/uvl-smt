package conversion;


import Reasoning.SMTSatisfiabilityChecker;
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

    @BeforeEach
    void setup() throws InvalidConfigurationException {
        this.context = SolverContextFactory.createSolverContext(Configuration.defaultConfiguration(), LogManager.createNullLogManager(), ShutdownManager.create().getNotifier(), SolverContextFactory.Solvers.Z3);
        this.booleanManager = context.getFormulaManager().getBooleanFormulaManager();
    }
    @Test
    void testCardinalities() {
        List<String> variables = new ArrayList<>();
        variables.add("a");
        variables.add("b");
        variables.add("c");
        variables.add("d");
        variables.add("e");

        BooleanFormula cardinality23 = buildCardinality(variables, 2 , 3);

        // [2,3] & 2 selected == SAT
        BooleanFormula satAssignment11 = buildSimpleAssignment(variables, 2, 3);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, satAssignment11), context);

        // [2,3] & 3 selected == SAT
        BooleanFormula satAssignment12 = buildSimpleAssignment(variables, 3, 1);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, satAssignment12), context);

        // [2,3] & 4 selected == !SAT
        BooleanFormula unsatAssignment11 = buildSimpleAssignment(variables, 4, 1);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, unsatAssignment11), context);

        // [2,3] & 4 deselected == !SAT
        BooleanFormula unsatAssignment12 = buildSimpleAssignment(variables, 1, 4);
        assert !SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality23, unsatAssignment12), context);


        BooleanFormula cardinality14 = buildCardinality(variables, 1, 4);

        // [1,4] & 1 selected == SAT
        BooleanFormula satAssignment21 = buildSimpleAssignment(variables, 1, 4);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment21), context);

        // [1,4] & 3 selected == SAT
        BooleanFormula satAssignment22 = buildSimpleAssignment(variables, 3, 0);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment22), context);

        // [1,4] & 5 selected == !SAT
        BooleanFormula unsatAssignment21 = buildSimpleAssignment(variables, 5, 0);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment21), context);

        // [1,4] & 5 deselected == !SAT
        BooleanFormula unsatAssignment22 = buildSimpleAssignment(variables, 0, 5);
        assert SMTSatisfiabilityChecker.isSatStatic(booleanManager.and(cardinality14, satAssignment22), context);


    }

    private BooleanFormula buildCardinality(List<String> variables, int lower, int upper) {
        CardinalityConverter converter = new CardinalityConverter(variables, lower, upper, booleanManager);
        return converter.convertCardinality();
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
