package de.featjar.formula.computation.interactionfinder;

import de.featjar.base.FeatJAR;
import de.featjar.base.data.IntegerList;
import de.featjar.base.data.LexicographicIterator;
import de.featjar.formula.assignment.ABooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanClauseList;
import de.featjar.formula.assignment.BooleanSolution;

import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class IncInteractionFinderOnlyWorkingConfigurations extends AInteractionFinder {
    private ArrayList<Integer> errors = new ArrayList<>();
    private static final double limitFactor = 10.0 / Math.log(2);


    @Override
    public List<BooleanAssignment> find(int tmax) {
        if (failingConfs.isEmpty()) {
            return null;
        }
        verifyCounter = 0;
        lastMerge = null;

        @SuppressWarnings("unchecked")
        List<int[]>[] results = new List[tmax];
        BooleanAssignment[] mergedResults = new BooleanAssignment[tmax];
        for (int ti = 1; ti <= tmax; ++ti) {
            List<int[]> res = findT(ti);
            if (res != null) {
                mergedResults[ti - 1] = new BooleanAssignment(lastMerge);
                results[ti - 1] = res;
            }
        }

        int lastI = -1;

        loop:
        for (int i = tmax - 1; i >= 0; --i) {
            if (mergedResults[i] != null) {
                if (lastI == -1) {
                    lastI = i;
                } else {
                    final BooleanAssignment lastMergedResult = mergedResults[lastI];
                    final BooleanAssignment curMergedResult = mergedResults[i];
                    if (lastMergedResult.containsAll(curMergedResult)) {
                        if (!curMergedResult.containsAll(lastMergedResult)) {
                            final LinkedHashSet<int[]> exclude = new LinkedHashSet<>();
                            for (int[] r : results[lastI]) {
                                int[] nr = new int[r.length];
                                int nrIndex = 0;
                                for (int l : r) {
                                    if (!curMergedResult.contains(l)) {
                                        nr[nrIndex++] = l;
                                    }
                                }
                                if (nrIndex == 0) {
                                    continue loop;
                                }
                                nr = nrIndex == nr.length ? nr : Arrays.copyOf(nr, nrIndex);
                                exclude.add(nr);
                            }
                            final BooleanSolution complete = updater.complete(
                                            List.of(curMergedResult.get()), exclude, null)
                                    .orElse(null);
                            if (complete != null && verify(complete)) {
                                break loop;
                            }
                        }
                        lastI = i;
                    } else {
                        break loop;
                    }
                }
            }
        }

        final List<int[]> result = lastI == -1 ? null : results[lastI];
        return isPotentialInteraction(result)
                ? List.of(new BooleanAssignment(
                IntegerList.mergeInt(result.stream().collect(Collectors.toList()))))
                : null;
    }

    @Override
    protected List<int[]> findT(int t) {
        if (lastMerge != null && lastMerge.length <= t) {
            lastMerge = null;
        }

        List<int[]> curInteractionList = computePotentialInteractions(t);
        if (curInteractionList == null) {
            return null;
        }

        setConfigurationVerificationLimit((int) Math.ceil(limitFactor * Math.log(curInteractionList.size())));


        while (curInteractionList.size() > errors.size() //
                && verifyCounter < configurationVerificationLimit) {
            BooleanSolution bestConfig =
                    updater.complete(null, null, curInteractionList).orElse(null);
            if (bestConfig == null) {
                break;
            }

            Map<Boolean, List<int[]>> partitions = group(curInteractionList, bestConfig);
            List<int[]> include = partitions.get(Boolean.TRUE);
            List<int[]> exclude = partitions.get(Boolean.FALSE);
            int diff = Math.abs(include.size() - exclude.size());
            int lastDiff = diff;

            loop:
            while (verifyCounter < configurationVerificationLimit) {
                while (diff > 1) {
                    BooleanSolution config;
                    if (include.size() > exclude.size()) {
                        config = updater.complete(null, exclude, include).orElse(null);
                        if (config == null) {
                            break;
                        }
                        partitions = group(include, config);
                        assert partitions.get(Boolean.FALSE) != null;
                        assert partitions.get(Boolean.TRUE) != null;
                        diff = Math.abs(
                                (exclude.size() + partitions.get(Boolean.FALSE).size())
                                        - partitions.get(Boolean.TRUE).size());
                        if (diff >= lastDiff) {
                            break;
                        }
                        exclude.addAll(partitions.get(Boolean.FALSE));
                        include = partitions.get(Boolean.TRUE);
                    } else {
                        config = updater.complete(include, null, exclude).orElse(null);
                        if (config == null) {
                            break;
                        }
                        partitions = group(exclude, config);
                        assert partitions.get(Boolean.FALSE) != null;
                        assert partitions.get(Boolean.TRUE) != null;
                        diff = Math.abs(
                                (include.size() + partitions.get(Boolean.TRUE).size())
                                        - partitions.get(Boolean.FALSE).size());
                        if (diff >= lastDiff) {
                            break;
                        }
                        include.addAll(partitions.get(Boolean.TRUE));
                        exclude = partitions.get(Boolean.FALSE);
                    }
                    if (!configurationPool.contains(config)) {
                        lastDiff = diff;
                        bestConfig = config;
                    } else {
                        bestConfig =
                                updater.complete(null, null, null).orElse(null);
                        partitions = group(curInteractionList, bestConfig);
                        include = partitions.get(Boolean.TRUE);
                        exclude = partitions.get(Boolean.FALSE);
                        if (exclude == null) {
                            exclude = new ArrayList<>();
                        }
                        if (include == null) {
                            include = new ArrayList<>();
                        }
                        diff = Math.abs(include.size() - exclude.size());
                        lastDiff = diff;
                    }
                }

                final boolean pass = verify(bestConfig);
                if (pass) {
                    curInteractionList = exclude;
                    if (lastMerge != null && pass == bestConfig.containsAll(lastMerge)) {
                        lastMerge = null;
                    }
                    break loop;
                } else {
                    bestConfig =
                            updater.complete(null, null, null).orElse(null);
                    partitions = group(curInteractionList, bestConfig);
                    include = partitions.get(Boolean.TRUE);
                    exclude = partitions.get(Boolean.FALSE);
                    if (exclude == null) {
                        exclude = new ArrayList<>();
                    }
                    if (include == null) {
                        include = new ArrayList<>();
                    }
                    diff = Math.abs(include.size() - exclude.size());
                    lastDiff = diff;
                }
            }
            if(configurationVerificationLimit == verifyCounter){
                throw new RuntimeException();
            }
        }

        if (curInteractionList.isEmpty()) {
            return null;
        } else {
            lastMerge = IntegerList.mergeInt(curInteractionList);
            return curInteractionList;
        }
    }

    public void addConfigurations(List<? extends ABooleanAssignment> configurations) {
        configurations.stream().map(ABooleanAssignment::toSolution).forEach(this::initial_verify);
    }

    protected boolean initial_verify(BooleanSolution solution) {
        verifyCounter++;
        if (verifier.test(solution) == 0) {
            succeedingConfs.add(solution);
            return true;
        } else {
            failingConfs.add(solution);
            return false;
        }
    }

    protected boolean verify(BooleanSolution solution) {
        verifyCounter++;
        if (!configurationPool.contains(solution)) {
            configurationPool.add(solution);
        }
        final int error = verifier.test(solution);
        if (error == 0) {
            succeedingConfs.add(solution);
            return true;
        } else {
            if (!errors.contains(error)) {
                errors.add(error);
            }
            return false;
        }
    }
}
