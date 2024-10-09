# Scimitar

*Scimitar* is a tool for verifying the safety of distributed protocols based on the inductive proof decomposition technique, a compositional approach for developing and inductive invarisnt in a way that aids automated synthesis and interpretability of the inductive proof. It was primarily developed for targeting safety verification of distributed protocols, but works for any TLA+ specifications accepted by TLC. Correctness of discovered invariants are formally verified using the [TLA+ proof system](https://tla.msr-inria.inria.fr/tlaps/content/Home.html) (TLAPS).

## Setup

In order to run the tool you will need the following prerequisites:

- Java version >= 11
- Python 3 with pip installed
- Install Python dependencies with `python3 -m pip install -r requirements.txt`

Note that the scimitar tool makes use of a slightly modified version of the TLC model checker, whose source code can be found [here](https://github.com/will62794/tlaplus/tree/ce9e63ab5242a596b8dec15000b5ed5f97f63300). The binary of this modified version of TLC is included in this repo, so there is no need to download and build it manually.

## Example Usage

As a demonstration of using endive, you can run it on the [TwoPhase](benchmarks/TwoPhase.tla) benchmark, a TLA+ specification of the two-phase commit protocol. This will attempt to generate an inductive invariant for proving the [`TCConsistent`](https://github.com/will62794/endive/blob/master/benchmarks/TwoPhase.tla#L163-L168) safety property:

```bash
python3 scimitar.py --spec benchmarks/TwoPhase --seed 1 --num_simulate_traces 200000 --tlc_workers 6 --debug --target_sample_time_limit_ms 30000 --target_sample_states 200000 --opt_quant_minimize --k_cti_induction_depth 1 --ninvs 400000 --max_num_ctis_per_round 300 --save_dot --niters 5 --max_num_conjuncts_per_round 20 --num_ctigen_workers 7 --nrounds 45 --proof_tree_mode --auto_lemma_action_decomposition --enable_partitioned_state_caching  --cti_elimination_workers 1 --do_tlaps_induction_checks   --ninvs_per_iter_group 25000
```

As the tool runs, it dynamically synthesizes an inductive proof graph, which is a compositional way of representing an inductive invariant in terms of its lemma and action relative inductino dependencies. You can, for example, observe the graph as it is generated by opening `benchmarks/TwoPhase_ind-proof-tree-sd1.pdf`. An example of a completed proof graph for the `TwoPhase` protocol can be seen below:


<img src="notes/TwoPhase_ind-proof-tree-sd1.png" alt="TwoPhase Proof Graph" width="480">

This provides an intuitive way to understand the structure of the inductive invariant and proof, while also allowing for optimizations during synthesis.


<!-- 

When this run terminates, you should see output like the following, showing a candidate inductive invariant along with some other statistics about the run:
```
\* The inductive invariant candidate.
IndAuto ==
  /\ TCConsistent
  /\ Inv276_1_0_def
  /\ Inv45_1_1_def
  /\ Inv79_1_2_def
  /\ Inv349_1_3_def
  /\ Inv318_1_4_def
  /\ Inv331_1_5_def
  /\ Inv334_1_6_def
  /\ Inv386_1_7_def
  /\ Inv1896_2_8_def
  /\ Inv344_1_0_def
----------------------------------------
Initial random seed: 20
opt_quant_minimize: 0
Total number of CTIs eliminated: 10001
Total number of invariants generated: 1124
Total number of invariants checked: 4033
CTI generation duration: 20.689125 secs.
Invariant checking duration: 13.481307 secs.
CTI elimination checks duration: 48.955196 secs.
Total duration: 83.30 secs.
```

This generated inductive invariant is not necessarily a true inductive invariant, but one that endive reports as likely to be correct, based on probabilistic counterexample sampling.

In order to formally verify the correctness of this invariant, you will need to use TLAPS. You can see an example of a proof for an inductive invariant discovered by endive for the `TwoPhase` protocol benchmark [here](benchmarks/TwoPhase_IndProofs.tla). -->

## Command line options

```
python3 scimitar.py --spec benchmarks/<benchmark_name> [options]
```

Detailed command line options:
```
$ python3 endive.py -h
usage: endive.py [-h] --spec SPEC [--ninvs NINVS] [--niters NITERS] [--nrounds NROUNDS] [--seed SEED] [--num_simulate_traces NUM_SIMULATE_TRACES] [--simulate_depth SIMULATE_DEPTH]
                 [--tlc_workers TLC_WORKERS] [--java_exe JAVA_EXE] [--debug] [--cache_invs CACHE_INVS] [--cache_num_conjuncts CACHE_NUM_CONJUNCTS] [--load_inv_cache LOAD_INV_CACHE]
                 [--log_file LOG_FILE] [--save_result] [--opt_quant_minimize] [--try_final_minimize] [--results_dir RESULTS_DIR]

optional arguments:
  -h, --help            show this help message and exit
  --spec SPEC           Name of the protocol benchmark to run (given as 'benchmarks/<spec_name>').
  --ninvs NINVS         Maximum number of invariants to generate at each iteration.
  --niters NITERS       Maximum number of invariant generation iterations to run in each CTI elimination round.
  --nrounds NROUNDS     Maximum number of CTI elimination rounds to run.
  --seed SEED           Seed for RNG.
  --num_simulate_traces NUM_SIMULATE_TRACES
                        The maximum number of traces TLC will run when searching for counterexamples to inductions (CTIs).
  --simulate_depth SIMULATE_DEPTH
                        Maximum depth of counterexample to induction (CTI) traces to search for.
  --tlc_workers TLC_WORKERS
                        Number of TLC worker threads to use when checking candidate invariants.
  --java_exe JAVA_EXE   Path to Java binary.
  --debug               Output debug info to log.
  --cache_invs CACHE_INVS
                        Save generated invariants to the given file.
  --cache_num_conjuncts CACHE_NUM_CONJUNCTS
                        Number of conjuncts in generated invariants to be cached.
  --load_inv_cache LOAD_INV_CACHE
                        Load pre-generated invariants from a file.
  --log_file LOG_FILE   Log output file.
  --save_result         Whether to save result statistics to a file
  --opt_quant_minimize  Enable quantifier minimization optimization for faster invariant checking.
  --try_final_minimize  Attempt to minimize the final discovered invariant.
  --results_dir RESULTS_DIR
                        Directory to save results.
```

## Creating a new benchmark

To create a new benchmark, you will need to define two files inside the `benchmarks` directory:

-  `<spec>.tla`:  a TLA+ specification of your protocol, with initial state and next state relation defined as `Init` and `Next`, respectively.
-  `<spec>.config.json`: A configuration file for running endive on your specification.

The configuration file is a JSON file with the following required, top-level fields:

- `preds`: a list of atomic TLA+ state predicates that define the grammar over which to search for candidate invariants to be used as conjuncts of an overall inductive invariant.
- `safety`: a string giving the TLA+ definition of the safety property to be verified.
- `constants`: a list of TLC configuration constant instantiations used for model checking the specification.
- `quant_inv`: a quantifier template that will be prepended to the candidate invariants generated from the atomic predicates given in `preds`
- `model_consts`: string giving a list of CONSTANT model values that are instantiated.
- `typeok`: definition of the TLA+ type invariant predicate to use during invariant inference (e.g. `TypeOK`).

Typically the easiest way to create a new benchmark configuration is to start from an example such as [`TwoPhase.config.json`](benchmarks/TwoPhase.config.json) (with corresponding TLA+ spec, [`TwoPhase.tla`](benchmarks/TwoPhase.tla)) and modify it as needed.