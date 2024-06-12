package conversion;

import de.vill.model.Feature;
import de.vill.model.FeatureModel;
import de.vill.model.Group;
import de.vill.model.constraint.*;
import de.vill.model.expression.*;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

public class FmToSMTConverter {

    private FormulaManager formulaManager;

    private BooleanFormulaManager boolManager;

    private IntegerFormulaManager intManager;

    private RationalFormulaManager doubleManager;

    private FeatureModel featureModel;

    public FmToSMTConverter(FeatureModel featureModel) throws InvalidConfigurationException {
        this(SolverContextFactory.createSolverContext(Configuration.defaultConfiguration(), LogManager.createNullLogManager(), ShutdownManager.create().getNotifier(), SolverContextFactory.Solvers.Z3), featureModel);
    }

    public FmToSMTConverter(SolverContext context, FeatureModel featureModel) throws InvalidConfigurationException {
        this.formulaManager = context.getFormulaManager();
        this.boolManager = this.formulaManager.getBooleanFormulaManager();
        this.intManager = this.formulaManager.getIntegerFormulaManager();
        this.doubleManager = this.formulaManager.getRationalFormulaManager();
        this.featureModel = featureModel;
    }

    public BooleanFormula convertFeatureModel() {
        return boolManager.and(convertTree(), convertConstraints());
    }

    public BooleanFormula convertTree() {
        List<BooleanFormula> formulaParts = new ArrayList<>();
        for (Feature feature : featureModel.getFeatureMap().values()) {
            if (feature.getParentGroup() == null) { // Root
                formulaParts.add(boolManager.makeVariable(feature.getIdentifier()));
            } else {
                formulaParts.add(boolManager.implication(boolManager.makeVariable(feature.getIdentifier()), boolManager.makeVariable(feature.getParentFeature().getIdentifier())));
                for (Group group : feature.getChildren()) {
                    formulaParts.add(convertGroup(group));
                }
            }
        }
        return boolManager.and(formulaParts);
    }

    public BooleanFormula convertConstraints() {
        List<BooleanFormula> formulaParts = new ArrayList<>();
        for (Constraint constraint : featureModel.getOwnConstraints()) {
            formulaParts.add(convertConstraintToSMT(constraint));
        }
        return boolManager.and(formulaParts);
    }

    public BooleanFormula convertGroup(Group group) {
        BooleanFormula groupConstraint;
        List<BooleanFormula> variables = group.getFeatures().stream().map(x -> boolManager.makeVariable(x.getIdentifier())).collect(Collectors.toList());
        if (group.GROUPTYPE == Group.GroupType.OR) {
            groupConstraint = boolManager.or(variables);
        } else if (group.GROUPTYPE == Group.GroupType.MANDATORY) {
            groupConstraint = boolManager.and(variables);
        } else if (group.GROUPTYPE == Group.GroupType.ALTERNATIVE) {
            groupConstraint = boolManager.or(variables); // TODO: Replace
        } else {
            return boolManager.makeTrue(); // Optional
        }
        return boolManager.implication(boolManager.makeVariable(group.getParentFeature().getIdentifier()), groupConstraint);
    }

    public BooleanFormula convertConstraintToSMT(Constraint constraint) {
        if (constraint instanceof AndConstraint) {
            AndConstraint andConstraint = (AndConstraint) constraint;
            return boolManager.and(convertConstraintToSMT(andConstraint.getLeft()), convertConstraintToSMT(andConstraint.getRight()));
        } else if (constraint instanceof OrConstraint) {
            OrConstraint orConstraint = (OrConstraint) constraint;
            return boolManager.or(convertConstraintToSMT(orConstraint.getLeft()), convertConstraintToSMT(orConstraint.getRight()));
        } else if (constraint instanceof NotConstraint) {
            NotConstraint notConstraint = (NotConstraint) constraint;
            return boolManager.not(convertConstraintToSMT(notConstraint.getContent()));
        } else if (constraint instanceof EquivalenceConstraint) {
            EquivalenceConstraint equivalenceConstraint = (EquivalenceConstraint) constraint;
            return boolManager.equivalence(convertConstraintToSMT(equivalenceConstraint.getLeft()), convertConstraintToSMT(equivalenceConstraint.getRight()));
        } else if (constraint instanceof ImplicationConstraint) {
            ImplicationConstraint implicationConstraint = (ImplicationConstraint) constraint;
            return boolManager.implication(convertConstraintToSMT(implicationConstraint.getLeft()), convertConstraintToSMT(implicationConstraint.getRight()));
        } else if (constraint instanceof ParenthesisConstraint) {
            ParenthesisConstraint parenthesisConstraint = (ParenthesisConstraint) constraint;
            return convertConstraintToSMT(parenthesisConstraint.getContent());
        } else if (constraint instanceof EqualEquationConstraint) {
            EqualEquationConstraint equalEquationConstraint = (EqualEquationConstraint) constraint;
            return intManager.equal(convertExpressionToSMT(equalEquationConstraint.getLeft()), convertExpressionToSMT(equalEquationConstraint.getRight()));
        } else if (constraint instanceof GreaterEqualsEquationConstraint) {
            GreaterEqualsEquationConstraint equalEquationConstraint = (GreaterEqualsEquationConstraint) constraint;
            return intManager.greaterOrEquals(convertExpressionToSMT(equalEquationConstraint.getLeft()), convertExpressionToSMT(equalEquationConstraint.getRight()));
        } else if (constraint instanceof LowerEqualsEquationConstraint) {
            LowerEqualsEquationConstraint equalEquationConstraint = (LowerEqualsEquationConstraint) constraint;
            return intManager.lessOrEquals(convertExpressionToSMT(equalEquationConstraint.getLeft()), convertExpressionToSMT(equalEquationConstraint.getRight()));
        } else if (constraint instanceof LowerEquationConstraint) {
            LowerEquationConstraint equalEquationConstraint = (LowerEquationConstraint) constraint;
            return intManager.lessThan(convertExpressionToSMT(equalEquationConstraint.getLeft()), convertExpressionToSMT(equalEquationConstraint.getRight()));
        } else if (constraint instanceof GreaterEquationConstraint) {
            GreaterEquationConstraint equalEquationConstraint = (GreaterEquationConstraint) constraint;
            return intManager.greaterThan(convertExpressionToSMT(equalEquationConstraint.getLeft()), convertExpressionToSMT(equalEquationConstraint.getRight()));
        } else if (constraint instanceof NotEqualsEquationConstraint) {
            NotEqualsEquationConstraint equalEquationConstraint = (NotEqualsEquationConstraint) constraint;
            return boolManager.not(intManager.equal(convertExpressionToSMT(equalEquationConstraint.getLeft()), convertExpressionToSMT(equalEquationConstraint.getRight())));
        } else if (constraint instanceof LiteralConstraint) {
            return boolManager.makeVariable(((LiteralConstraint) constraint).getReference().getIdentifier());
        } else {
            return null;
        }
    }

    // TODO: Aggregates missing
    public NumeralFormula.IntegerFormula convertExpressionToSMT(Expression expression) {
        if (expression instanceof AddExpression) {
            AddExpression addExpression = (AddExpression) expression;
            return intManager.add(convertExpressionToSMT(addExpression.getLeft()), convertExpressionToSMT(addExpression.getRight()));
        } else if (expression instanceof SubExpression) {
            SubExpression subExpression = (SubExpression) expression;
            return intManager.subtract(convertExpressionToSMT(subExpression.getLeft()), convertExpressionToSMT(subExpression.getRight()));
        } else if (expression instanceof MulExpression) {
            MulExpression mulExpression = (MulExpression) expression;
            return intManager.multiply(convertExpressionToSMT(mulExpression.getLeft()), convertExpressionToSMT(mulExpression.getRight()));
        } else if (expression instanceof DivExpression) {
            DivExpression divExpression = (DivExpression) expression;
            return intManager.divide(convertExpressionToSMT(divExpression.getLeft()), convertExpressionToSMT(divExpression.getRight()));
        } else if (expression instanceof  LiteralExpression) {
            LiteralExpression literalExpression = (LiteralExpression) expression;
            return intManager.makeVariable(literalExpression.getContent().getIdentifier());
        } else if (expression instanceof NumberExpression) {
            NumberExpression numberExpression = (NumberExpression) expression;
            return intManager.makeNumber(numberExpression.getNumber());
        } else {
            return null;
        }
    }
}
