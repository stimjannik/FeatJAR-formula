package org.spldev.formula.structure.atomic.literal;

import java.util.*;

import org.spldev.formula.structure.atomic.*;

/**
 * A special {@link Atomic} that is always {@code false}.
 *
 * @author Sebastian Krieter
 */
public class False extends Literal {

	private static final False INSTANCE = new False();

	private False() {
		super();
	}

	public static False getInstance() {
		return INSTANCE;
	}

	@Override
	public True flip() {
		return Literal.True;
	}

	@Override
	public False cloneNode() {
		return this;
	}

	@Override
	public String getName() {
		return "false";
	}

	@Override
	public int hashCode() {
		return 27 * Objects.hashCode(getName());
	}

	@Override
	public boolean equals(Object other) {
		return other == INSTANCE;
	}

	@Override
	public boolean equalsNode(Object other) {
		return other == INSTANCE;
	}

	@Override
	public String toString() {
		return "false";
	}

}
