/*
 * Copyright (C) 2024 FeatJAR-Development-Team
 *
 * This file is part of FeatJAR-formula.
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
package de.featjar.formula.computation.interactionfinder;

import de.featjar.analysis.IConfigurationUpdater;
import de.featjar.analysis.IConfigurationVerifyer;
import de.featjar.base.data.IntegerList;
import de.featjar.base.data.LexicographicIterator;
import de.featjar.formula.assignment.ABooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanSolution;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

/**
 * @author Tim Jannik Schmidt
 */
public abstract class AInteractionFinder {
    protected IConfigurationUpdater updater;
    protected IConfigurationVerifyer verifier;
    private ABooleanAssignment core;

    protected int configurationVerificationLimit = Integer.MAX_VALUE;

    protected List<BooleanSolution> succeedingConfs;
    protected List<BooleanSolution> failingConfs;

    protected int verifyCounter;
    protected int[] lastMerge;

    public void reset() {
        succeedingConfs = new ArrayList<>();
        failingConfs = new ArrayList<>();
    }

    public void setUpdater(IConfigurationUpdater updater) {
        this.updater = updater;
    }

    public void setVerifier(IConfigurationVerifyer verifier) {
        this.verifier = verifier;
    }

    public void setCore(ABooleanAssignment core) {
        this.core = core;
    }

    public void setConfigurationVerificationLimit(int configurationVerificationLimit) {
        this.configurationVerificationLimit = configurationVerificationLimit;
    }

    public void addConfigurations(List<? extends ABooleanAssignment> configurations) {
        configurations.stream().map(ABooleanAssignment::toSolution).forEach(this::verify);
    }

    public abstract List<BooleanAssignment> find(int tmax);

    public List<BooleanSolution> getSample() {
        ArrayList<BooleanSolution> sample = new ArrayList<>(succeedingConfs.size() + failingConfs.size());
        sample.addAll(succeedingConfs);
        sample.addAll(failingConfs);
        return sample;
    }

    public int getVerifyCounter() {
        return verifyCounter;
    }

    protected List<int[]> computePotentialInteractions(int t) {
        final Iterator<BooleanSolution> iterator = failingConfs.iterator();
        ABooleanAssignment failingLiterals = iterator.next();
        while (iterator.hasNext()) {
            failingLiterals = new BooleanAssignment(iterator.next().retainAll(failingLiterals.get()));
        }
        if (core != null) {
            failingLiterals = new BooleanAssignment(failingLiterals.removeAll(core.get()));
        }

        final int[] commonLiterals = failingLiterals.toAssignment().get();
        if (commonLiterals.length < t) {
            return List.of(commonLiterals);
        }

        Stream<int[]> stream = LexicographicIterator.parallelStream(t, commonLiterals.length) //
                .map(combo -> combo.getSelection(commonLiterals));
        List<int[]> interactions;
        if (lastMerge != null) {
            BooleanAssignment lastLiterals = new BooleanAssignment(lastMerge);
            if (lastLiterals.containsAll(failingLiterals)) {
                return null;
            }
            interactions = stream //
                    .filter(literals -> !lastLiterals.containsAll(literals)) //
                    .filter(literals -> !isCovered(literals)) //
                    .map(literals -> Arrays.copyOf(literals, literals.length)) //
                    .collect(Collectors.toList());
            interactions.add(lastMerge);
        } else {
            interactions = stream //
                    .filter(literals -> !isCovered(literals)) //
                    .map(literals -> Arrays.copyOf(literals, literals.length)) //
                    .collect(Collectors.toList());
        }
        return interactions;
    }

    protected abstract List<int[]> findT(int t);

    private boolean isCovered(int[] combo) {
        for (BooleanSolution configuration : succeedingConfs) {
            if (configuration.containsAll(combo)) {
                return true;
            }
        }
        return false;
    }

    protected Map<Boolean, List<int[]>> group(List<int[]> list, final BooleanSolution newConfig) {
        return list.parallelStream()
                .collect(Collectors.groupingByConcurrent(
                        i -> newConfig.containsAll(i), Collectors.toCollection(ArrayList::new)));
    }

    protected boolean verify(BooleanSolution solution) {
        verifyCounter++;
        if (verifier.test(solution) == 0) {
            succeedingConfs.add(solution);
            return true;
        } else {
            failingConfs.add(solution);
            return false;
        }
    }

    protected boolean isPotentialInteraction(List<int[]> interactions) {
        if (interactions == null) {
            return false;
        }
        final BooleanSolution testConfig =
                updater.complete(interactions, null, null).orElse(null);
        if (testConfig == null || verify(testConfig)) {
            return false;
        }
        int[] exclude = IntegerList.mergeInt(interactions);
        final BooleanSolution inverseConfig =
                updater.complete(null, List.of(exclude), null).orElse(null);
        return inverseConfig == null || verify(inverseConfig);
    }
}
