package Reasoning;

import org.sosy_lab.java_smt.api.*;

public class SMTSatisfiabilityChecker {

    ProverEnvironment prover;
    BooleanFormula baseFormula;

    public SMTSatisfiabilityChecker(BooleanFormula baseFormula, SolverContext context) {
        this.prover = context.newProverEnvironment(SolverContext.ProverOptions.GENERATE_MODELS);
        try {
            prover.addConstraint(baseFormula);
        } catch (InterruptedException e) {
            throw new RuntimeException(e);
        }
    }

    public boolean checkAndKeepIfSatisfiable(BooleanFormula formula) {
        try {
            prover.addConstraint(baseFormula);
            boolean sat = !prover.isUnsat();
            if (!sat) prover.pop();
            return sat;
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
