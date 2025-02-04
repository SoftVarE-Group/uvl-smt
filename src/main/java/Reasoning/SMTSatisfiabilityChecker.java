package Reasoning;

import org.sosy_lab.java_smt.api.*;

public class SMTSatisfiabilityChecker {

    ProverEnvironment prover;
    BooleanFormula baseFormula;

    public SMTSatisfiabilityChecker(BooleanFormula baseFormula, SolverContext context) {
        this.prover = context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS);
        this.baseFormula = baseFormula;
        try {
            prover.addConstraint(baseFormula);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    /**
     * Checks the satisfiability of baseFormula & formula and only pops the formula from the solver if it is unsat
     * @param formula to check in context of baseFormula
     * @return true if sat
     */
    public boolean checkAndKeepIfSatisfiable(BooleanFormula formula) {
        try {
            prover.push(formula);
            boolean sat = !prover.isUnsat();
            if (!sat) prover.pop();
            return sat;
        } catch (SolverException | InterruptedException e) {
            System.out.println(e.getMessage());
            throw new RuntimeException(e);
        }
    }

    /**
     * Checks the satisfiability of baseFormula & formula and then pops formula from the solver again
     * @param formula to check in context of baseFormula
     * @return true if sat
     */
    public boolean isSatWith(BooleanFormula formula) {
        try {
            prover.push(formula);
            boolean sat = !prover.isUnsat();
            prover.pop();
            return sat;
        } catch (SolverException | InterruptedException e) {
            System.out.println(e.getMessage());
            throw new RuntimeException(e);
        }
    }

    /**
     * Checks satisfiability of baseformula
     * @return true if sat
     */
    public boolean isSat() {
        try {
            return !prover.isUnsat();
        } catch (SolverException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public static boolean isSatStatic(BooleanFormula booleanFormula, SolverContext context) {
        try (ProverEnvironment prover = context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS)) {
            prover.addConstraint(booleanFormula);
            return !prover.isUnsat();
        } catch (SolverException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}
