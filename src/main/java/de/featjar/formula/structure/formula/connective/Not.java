/*
 * Copyright (C) 2022 Sebastian Krieter, Elias Kuiter
 *
 * This file is part of formula.
 *
 * formula is free software: you can redistribute it and/or modify it
 * under the terms of the GNU Lesser General Public License as published by
 * the Free Software Foundation, either version 3.0 of the License,
 * or (at your option) any later version.
 *
 * formula is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.
 * See the GNU Lesser General Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public License
 * along with formula. If not, see <https://www.gnu.org/licenses/>.
 *
 * See <https://github.com/FeatureIDE/FeatJAR-formula> for further information.
 */
package de.featjar.formula.structure.formula.connective;

import de.featjar.formula.structure.Expression;
import de.featjar.formula.structure.NonTerminalExpression;
import de.featjar.formula.structure.UnaryExpression;

import java.util.List;

/**
 * Expresses "not A" constraints (i.e., negation).
 * Evaluates to {@code true} iff its child evaluates to {@code false}.
 *
 * @author Sebastian Krieter
 */
public class Not extends NonTerminalExpression implements Connective, UnaryExpression {
    protected Not() {
    }

    public Not(Expression expression) {
        super(expression);
    }

    public Not(List<? extends Expression> formulas) {
        super(formulas);
    }

    @Override
    public String getName() {
        return "not";
    }

    @Override
    public Object evaluate(List<?> values) {
        return !(boolean) values.get(0);
    }

    @Override
    public Not cloneNode() {
        return new Not();
    }
}
