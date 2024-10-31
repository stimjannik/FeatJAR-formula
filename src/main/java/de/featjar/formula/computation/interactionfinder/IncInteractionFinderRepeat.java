package de.featjar.formula.computation.interactionfinder;

import de.featjar.base.FeatJAR;
import de.featjar.base.data.IntegerList;
import de.featjar.formula.assignment.ABooleanAssignment;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanSolution;

import java.util.*;
import java.util.stream.Collectors;

public class IncInteractionFinderRepeat extends AInteractionFinder {
    private ArrayList<Integer> errors = new ArrayList<>();
    private List<BooleanSolution> differentErrorConfs = new ArrayList<>();

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

//                            while (true) {
                            final BooleanSolution complete = updater.complete(
                                            List.of(curMergedResult.get()), exclude, null)
                                    .orElse(null);
                            try {
                                if (complete != null && verify(complete)) {
                                    break loop;
                                }
//                                    break;
                            } catch (DifferentErrorException e) {
                                break loop;
                            }
//                            }
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

        while (curInteractionList.size() > 1 //
                && verifyCounter < configurationVerificationLimit) {
            BooleanSolution bestConfig =
                    updater.complete(null, deepCopyList(configurationPool), curInteractionList).orElse(null);
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

                        List<int[]> copy = deepCopyList(exclude);
                        copy.addAll(deepCopyList(configurationPool));

                        config = updater.complete(null, copy, include).orElse(null);
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
                        config = updater.complete(include, deepCopyList(configurationPool), exclude).orElse(null);
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
                        lastDiff = diff;
                        bestConfig = config;
                }

                try {
                    final boolean pass = verify(bestConfig);
                    curInteractionList = pass ? exclude : include;
                    if (lastMerge != null && pass == bestConfig.containsAll(lastMerge)) {
                        lastMerge = null;
                    }
                    break loop;
                } catch (DifferentErrorException e) {
                    break loop;
                }
            }
        }

        if (curInteractionList.isEmpty()) {
            return null;
        } else {
            lastMerge = IntegerList.mergeInt(curInteractionList);
            return curInteractionList;
        }
    }

    protected boolean verify(BooleanSolution solution) throws DifferentErrorException {
        verifyCounter++;
        if (!configurationPool.contains(solution)) {
            configurationPool.add(solution.get().clone());
        }
        int error = verifier.test(solution);
        boolean result;
        if (error == 0) {
            succeedingConfs.add(solution);
            result = true;
        } else {
            if (errors.isEmpty()) {
                errors.add(error);
            }
            if (error == errors.get(0)) {
                failingConfs.add(solution);
                result = false;
            } else {
                differentErrorConfs.add(solution);
                throw new DifferentErrorException(Integer.toString(error));
            }
        }
        return result;
    }

    protected boolean isPotentialInteraction(List<int[]> interactions) {
        if (interactions == null) {
            System.out.println("no interactions found! :(");
            return false;
        }

        while (true) {
            try {
                final BooleanSolution testConfig =
                        updater.complete(interactions, null, null).orElse(null);
                if (testConfig == null || verify(testConfig)) {
                    return false;
                }
                break;
            } catch (DifferentErrorException e) {
                //
            }
        }

        boolean result;

        try {
            int[] exclude = IntegerList.mergeInt(interactions);
            final BooleanSolution inverseConfig =
                    updater.complete(null, List.of(exclude), null).orElse(null);
            result = inverseConfig == null || verify(inverseConfig);
        } catch (DifferentErrorException e) {
            result = true;
        }

        return result;
    }

    private List<int[]> deepCopyList(List<int[]> originalList) {
        List<int[]> copy = new ArrayList<>(originalList.size());
        for (int[] array : originalList) {
            copy.add(array.clone());
        }
        return copy;
    }
}
