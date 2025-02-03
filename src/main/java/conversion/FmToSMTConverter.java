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
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

public class FmToSMTConverter {

    private final FormulaManager formulaManager;

    private final BooleanFormulaManager boolManager;

    private final IntegerFormulaManager intManager;

    private final RationalFormulaManager doubleManager;

    private final StringFormulaManager stringManager;

    private final FeatureModel featureModel;

    private final SolverContext context;

    private Map<String, List<BooleanFormula>> attributeAverageSetters;

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
        this.attributeAverageSetters = new HashMap<>();
    }

    public BooleanFormula convertFeatureModel() {
        return boolManager.and(convertTree(), convertConstraints());
    }

    public BooleanFormula convertTree() {
        List<BooleanFormula> formulaParts = new ArrayList<>();
        for (Feature feature : featureModel.getFeatureMap().values()) {
            BooleanFormula featureVariable = boolManager.makeVariable(feature.getIdentifier());
            if (feature.getParentGroup() == null) { // Root
                formulaParts.add(featureVariable);
            } else {
                formulaParts.add(boolManager.implication(featureVariable, boolManager.makeVariable(feature.getParentFeature().getIdentifier())));
            }
            for (Group group : feature.getChildren()) {
                formulaParts.add(convertGroup(group));
            }
            for (Attribute<?> att : feature.getAttributes().values()) {
                if (att.getType().equals(Constants.NUMBER)) { // TODO: Only needed if attribute appears in constraint
                    NumeralFormula.IntegerFormula attributeVariable = intManager.makeVariable(getAttributeIdentifier(feature, att));
                    BooleanFormula selectedImplication = boolManager.implication(featureVariable, intManager.equal(attributeVariable, intManager.makeNumber((int) att.getValue())));
                    formulaParts.add(selectedImplication);
                    BooleanFormula unselectedImplication = boolManager.implication(boolManager.not(featureVariable), intManager.equal(attributeVariable, intManager.makeNumber(0)));
                    formulaParts.add(unselectedImplication);
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
        for (List<BooleanFormula> set : attributeAverageSetters.values()) {
            formulaParts.addAll(set);
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
                for (int j = i + 1; j < variables.size(); j++) {
                    pairClauses.add(boolManager.or(boolManager.not(boolManager.makeVariable(group.getFeatures().get(i).getIdentifier())), boolManager.not(boolManager.makeVariable(group.getFeatures().get(j).getIdentifier()))));
                }
            }
            pairClauses.add(atLeastOne);
            groupConstraint = boolManager.and(pairClauses);
        } else if (group.GROUPTYPE == Group.GroupType.GROUP_CARDINALITY) {
            CardinalityConverter converter = new CardinalityConverter(group.getCardinality().upper, group.getCardinality().lower, group.getFeatures(), boolManager);
            groupConstraint = converter.convertCardinality();
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
            if (literalExpression.getContent() instanceof Attribute<?>) {
                Attribute<?> attribute = (Attribute<?>) literalExpression.getContent();
                return intManager.makeVariable(getAttributeIdentifier(attribute.getFeature(), attribute));
            }
            return intManager.makeVariable(literalExpression.getContent().getIdentifier()); // Feature
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
                attributes.add(intManager.makeVariable(getAttributeIdentifier(feature, feature.getAttributes().get(attributeName))));
            }
        }
        return intManager.sum(attributes);
    }

    public NumeralFormula.IntegerFormula convertAvgAggregate(AvgAggregateFunctionExpression aggregate) {
        String attributeName = aggregate.getAttribute().getIdentifier();
        List<NumeralFormula.IntegerFormula> attributes = new ArrayList<>();
        List<NumeralFormula.IntegerFormula> dividers = new ArrayList<>();
        List<BooleanFormula> setters = new ArrayList<>();
        for (Feature feature : featureModel.getFeatureMap().values()) {
            if (feature.getAttributes().containsKey(attributeName)) {
                attributes.add(intManager.makeVariable(getAttributeIdentifier(feature, feature.getAttributes().get(attributeName))));
                NumeralFormula.IntegerFormula dividerVariable = intManager.makeVariable(feature.getIdentifier() + "_" + "AVG_INT");
                dividers.add(dividerVariable);
                if (!attributeAverageSetters.containsKey(attributeName)) {
                    setters.add(boolManager.implication(boolManager.makeVariable(feature.getIdentifier()), intManager.equal(dividerVariable, intManager.makeNumber(1))));
                    setters.add(boolManager.implication(boolManager.not(boolManager.makeVariable(feature.getIdentifier())), intManager.equal(dividerVariable, intManager.makeNumber(0))));
                }
            }
        }
        if (dividers.isEmpty()) return intManager.makeNumber(0);
        if (!attributeAverageSetters.containsKey(attributeName)) {
            attributeAverageSetters.put(attributeName, setters);
        }
        return intManager.divide(intManager.sum(attributes), intManager.sum(dividers));
    }

    private static String getAttributeIdentifier(Feature feature, Attribute<?> attribute) {
        return feature.getIdentifier() + "." + attribute.getName();
    }

}
