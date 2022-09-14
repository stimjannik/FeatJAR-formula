package de.featjar.formula.structure.formula;

import de.featjar.formula.structure.Expression;
import de.featjar.formula.structure.assignment.Assignment;
import de.featjar.formula.structure.formula.predicate.False;
import de.featjar.formula.structure.formula.predicate.Predicate;
import de.featjar.formula.structure.formula.predicate.True;
import de.featjar.formula.structure.term.value.Variable;
import de.featjar.formula.tmp.ValueVisitor;

/**
 * A well-formed formula.
 * Evaluates to either {@code true} or {@code false}.
 * In a formula, each {@link Variable} can, but does not have to be bound by a
 * {@link de.featjar.formula.structure.formula.connective.Quantifier}.
 * A formula is either a {@link de.featjar.formula.structure.formula.connective.Connective}
 * or a {@link Predicate}.
 *
 * @author Sebastian Krieter
 * @author Elias Kuiter
 */
public interface Formula extends Expression {
    /**
     * A tautology.
     */
    True TRUE = True.getInstance();

    /**
     * A contradiction.
     */
    False FALSE = False.getInstance();

    default Class<?> getType() {
        return Boolean.class;
    }

    /**
     * {@return the evaluation of this formula on a given assignment}
     *
     * @param assignment the assignment
     */
    default Boolean evaluate(Assignment assignment) {
        return (Boolean) traverse(new ValueVisitor(assignment)).orElse(null);
    }
}
