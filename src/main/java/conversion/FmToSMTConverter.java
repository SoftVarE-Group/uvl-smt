package conversion;

import de.vill.model.*;
import de.vill.model.constraint.*;
import de.vill.model.expression.*;
import de.vill.util.Constants;
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

    private StringFormulaManager stringManager;

    private FeatureModel featureModel;

    private SolverContext context;

    public SolverContext getContext() {return context;}

    public FmToSMTConverter(FeatureModel featureModel) throws InvalidConfigurationException {
        this(SolverContextFactory.createSolverContext(Configuration.defaultConfiguration(), LogManager.createNullLogManager(), ShutdownManager.create().getNotifier(), SolverContextFactory.Solvers.Z3), featureModel);
    }

    public FmToSMTConverter(SolverContext context, FeatureModel featureModel) throws InvalidConfigurationException {
        this.context = context;
        this.formulaManager = context.getFormulaManager();
        this.boolManager = this.formulaManager.getBooleanFormulaManager();
        this.intManager = this.formulaManager.getIntegerFormulaManager();
        this.doubleManager = this.formulaManager.getRationalFormulaManager();
        this.stringManager = this.formulaManager.getStringFormulaManager();
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
            BooleanFormula atLeastOne = boolManager.or(variables);
            List<BooleanFormula> pairClauses = new ArrayList<>();
            for (int i = 0; i < group.getFeatures().size(); i++) {
                for (int j = i; j < variables.size(); j++) {
                    pairClauses.add(boolManager.or(boolManager.not(boolManager.makeVariable(group.getFeatures().get(i).getIdentifier())), boolManager.not(boolManager.makeVariable(group.getFeatures().get(j).getIdentifier()))));
                }
            }
            pairClauses.add(atLeastOne);
            groupConstraint = boolManager.and(pairClauses);
        } else if (group.GROUPTYPE == Group.GroupType.GROUP_CARDINALITY) { // TODO: is this even correct, assumes that managers share variables by identifier
            List<NumeralFormula.IntegerFormula> intVariables = group.getFeatures().stream().map(x -> intManager.makeVariable(x.getIdentifier())).collect(Collectors.toList());
            BooleanFormula lower = intManager.greaterOrEquals(intManager.sum(intVariables), intManager.makeNumber(group.getCardinality().lower));
            BooleanFormula upper = intManager.greaterOrEquals(intManager.makeNumber(group.getCardinality().upper), intManager.sum(intVariables));
            groupConstraint = boolManager.and(lower, upper);
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
            StringFormula left = getStringExpressionIfEligible(equalEquationConstraint.getLeft());
            StringFormula right = getStringExpressionIfEligible(equalEquationConstraint.getRight());
            if (left != null && right != null) {
                return stringManager.equal(left, right);
            }
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
        } else if (expression instanceof SumAggregateFunctionExpression){
            return convertSumAggregate((SumAggregateFunctionExpression) expression);
        } else if (expression instanceof AvgAggregateFunctionExpression) {
            return convertAvgAggregate((AvgAggregateFunctionExpression) expression);
        } else if (expression instanceof LengthAggregateFunctionExpression) {
            LengthAggregateFunctionExpression lengthAggregateFunctionExpression = (LengthAggregateFunctionExpression) expression;
            return intManager.makeVariable(lengthAggregateFunctionExpression.getReference().getIdentifier() + "-len");
        } else {
            return null;
        }
    }


    private StringFormula getStringExpressionIfEligible(Expression expression) {
        if (expression instanceof StringExpression) return stringManager.makeString(((StringExpression) expression).getString());
        if (expression instanceof LiteralExpression) {
            LiteralExpression literalExpression = (LiteralExpression) expression;
            if (literalExpression.getContent() instanceof Feature) {
                if (((Feature)literalExpression.getContent()).getFeatureType() == FeatureType.STRING) return stringManager.makeVariable(literalExpression.getContent().getIdentifier() + "-str"); // adapted name to differentiate between boolean feature
            }
            if (literalExpression.getContent() instanceof Attribute<?>) {
                if (((Attribute<?>)literalExpression.getContent()).getType().equals(Constants.STRING)) return stringManager.makeVariable(literalExpression.getContent().getIdentifier());
            }
        }
        return null;
    }


    public NumeralFormula.IntegerFormula convertSumAggregate(SumAggregateFunctionExpression aggregate) {
        String attributeName = aggregate.getAttribute().getIdentifier();
        List<NumeralFormula.IntegerFormula> attributes = new ArrayList<>();
        for (Feature feature : featureModel.getFeatureMap().values()) {
            if (feature.getAttributes().containsKey(attributeName)) {
                attributes.add(intManager.multiply(intManager.makeVariable(feature.getIdentifier()), intManager.makeVariable(feature.getAttributes().get(attributeName).getIdentifier())));
            }
        }
        return intManager.sum(attributes);
    }

    public NumeralFormula.IntegerFormula convertAvgAggregate(AvgAggregateFunctionExpression aggregate) {
        String attributeName = aggregate.getAttribute().getIdentifier();
        List<NumeralFormula.IntegerFormula> attributes = new ArrayList<>();
        List<NumeralFormula.IntegerFormula> dividers = new ArrayList<>();
        for (Feature feature : featureModel.getFeatureMap().values()) {
            if (feature.getAttributes().containsKey(attributeName)) {
                attributes.add(intManager.multiply(intManager.makeVariable(feature.getIdentifier()), intManager.makeVariable(feature.getAttributes().get(attributeName).getIdentifier())));
                dividers.add(intManager.makeVariable(feature.getIdentifier()));
            }
        }
        if (dividers.isEmpty()) return intManager.makeNumber(0);
        return intManager.divide(intManager.sum(attributes), intManager.sum(dividers));
    }
}
