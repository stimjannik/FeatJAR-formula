/* -----------------------------------------------------------------------------
 * formula - Propositional and first-order formulas
 * Copyright (C) 2020 Sebastian Krieter
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
 * See <https://github.com/FeatJAR/formula> for further information.
 * -----------------------------------------------------------------------------
 */
package de.featjar.formula.io.textual;

import de.featjar.formula.structure.Formula;
import de.featjar.util.data.Result;
import de.featjar.util.io.InputMapper;
import de.featjar.util.io.format.Format;

public class FormulaFormat implements Format<Formula> {

	public static final String ID = FormulaFormat.class.getCanonicalName();

	@Override
	public Result<Formula> parse(InputMapper inputMapper) {
		return new NodeReader().read(inputMapper.get().readText().get());
	}

	@Override
	public String serialize(Formula object) {
		return new NodeWriter().write(object);
	}

	@Override
	public boolean supportsParse() {
		return true;
	}

	@Override
	public boolean supportsSerialize() {
		return true;
	}

	@Override
	public String getIdentifier() {
		return ID;
	}

	@Override
	public String getFileExtension() {
		return "formula";
	}

	@Override
	public String getName() {
		return "Formula";
	}

}
