
# Running the TLA+ Proof System (Tool)

You can invoke the TLA+ proof system (TLAPS) to check correctness of a proof obligation in a TLA+ spec file <spec> with command

```
/usr/local/bin/tlapm --threads 8 --toolbox <proof_obl_line> <proof_obl_line> <spec>
```

You can run the tools a few time to understand the output format which returns status about the obligations proven or failed. you can also use the `--stretch` flag to control the time spent on checking the proof if needed to expand timeouts. In general, try not to push stretch to values higher than 3, trying to rely on decomposition instead when possible.

Also, whenever you run the tlapm tool, try to record its output durably to a file somewhere, so that if you need to grep for failures/status info, you don't need to re-run the tool again. In addition, BE CAREFUL to make sure you include the correct line numbers when checking a sub-obligation within a larger hierarchical proof. Don't leave out missing lines at the end. BE CAREFUL WITH THIS, so you don't accidentally mark a sub-goal of a proof as checked even though you left out some of it in your line ranges.

IMPORTANT: Please do not use OMITTED to skip over proof obligations and leave them unproven.

## Decomposing proofs

If a proof obligation is unable to be proven automatically, you can try decomposing it into smaller steps and then trying to get the smaller steps to go through automatically. You can apply this process recursively until the proof obligations are small enough to be proven automatically.

Also, when decomposing a goal into a set of sub-goals, always make sure that to verify that the QED step of all the sub-goals checks properly, to make sure that the decomposition is actually correct, before trying to dive in to make sure all of the sub-goals themselves are correct.