package de.featjar.formula.computation.interactionfinder;

import de.featjar.base.data.IntegerList;
import de.featjar.formula.assignment.BooleanAssignment;
import de.featjar.formula.assignment.BooleanSolution;

import java.util.*;
import java.util.stream.Collectors;

public class IncInteractionFinderOnlyWorkingConfigurations extends AInteractionFinder {
    private ArrayList<Integer> errors = new ArrayList<>();

    @Override
    public List<BooleanAssignment> find(int tmax) {
//        if (failingConfs.isEmpty()) {
//            return null;
//        }
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
                lastDiff = diff;
                bestConfig = config;
            }

            final boolean pass = verify(bestConfig);
            curInteractionList = pass ? exclude : include;
            if (lastMerge != null && pass == bestConfig.containsAll(lastMerge)) {
                lastMerge = null;
            }
        }

        if (curInteractionList.isEmpty()) {
            return null;
        } else {
            lastMerge = IntegerList.mergeInt(curInteractionList);
            return curInteractionList;
        }
    }

    protected boolean verify(BooleanSolution solution) {
        verifyCounter++;
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
