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
package de.featjar.formula.structure.formula.predicate;

import de.featjar.formula.structure.BinaryExpression;
import de.featjar.formula.tmp.Formulas;

import java.util.List;

/**
 * A binary predicate.
 *
 * @author Elias Kuiter
 */
public interface BinaryPredicate extends Predicate, BinaryExpression {
    @SuppressWarnings({"unchecked", "rawtypes"})
    @Override
    default Boolean evaluate(List<?> values) {
        Formulas.assertInstanceOf(Comparable.class, values);
        final Comparable v1 = (Comparable) values.get(0);
        final Comparable v2 = (Comparable) values.get(1);
        return (v1 != null && v2 != null) ? compareDifference(v1.compareTo(v2)) : null;
    }

    boolean compareDifference(int difference);
}
