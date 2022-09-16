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
package de.featjar.formula.structure.term.function;

import de.featjar.formula.structure.term.Term;

import java.util.List;
import java.util.Objects;
import java.util.function.BinaryOperator;

/**
 * A function.
 * Functions (i.e., n-ary terms for n > 1) can be applied to terms
 * (i.e., another {@link Function} or a {@link de.featjar.formula.structure.term.value.Value}).
 *
 * @author Sebastian Krieter
 * @author Elias Kuiter
 */
public interface Function extends Term {
    /**
     * {@return a list of values reduced to a single value}
     *
     * @param values the values
     * @param binaryOperator the binary operator
     * @param <T> the type of the value
     */
    @SuppressWarnings("unchecked")
    static <T> T reduce(List<?> values, final BinaryOperator<T> binaryOperator) {
        if (values.stream().anyMatch(Objects::isNull)) {
            return null;
        }
        return values.stream().map(l -> (T) l).reduce(binaryOperator).orElse(null);
    }
}
