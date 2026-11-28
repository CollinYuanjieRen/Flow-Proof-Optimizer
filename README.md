# Flow Proof Optimizer

**Author: Yuanjie (Collin) Ren from Atomic Inference Inc.**

Flow Proof Optimizer finds unused and repeated derivations in Lean 4 projects. Give it a built project and the names of the theorems you care about. It traces their dependencies, locates candidate changes in the source, and gives you evidence to decide which changes to make. For supported patterns it can extract a shared lemma, compile the replacements at their original call sites, and replay their proof terms.

The scanners, patch generator, replay checks, and size measurements run locally with Python and Lean. An optional model interface supports mathematical review when a candidate needs an insight, such as recognizing that one implication follows from the other by an involution. Some upstream patches were written this way after deterministic discovery.

## Try it on a four-module project

Install elan with Lake and Python 3.11 or newer. The repository pins Lean 4.37.0-rc1, the version used for the examples below. Compile the scanner with the toolchain that produced the target project's artifacts. Other Lean releases may require changes to the expression or reference readers.

```sh
lake build proof-pairs
(cd examples/tiny && lake build)
python3 tools/workflow.py examples/tiny .flow/tiny --root Demo.result
```

Open `.flow/tiny/report.json`. The result depends on both `Demo.first` and `Demo.second`. The scanner finds two matching lines separated by a different first branch and records a dependency path to each proof. The fourth module, `Demo.Spare`, lies outside the root module's imports. Its theorem `Demo.unused` is a deletion candidate. You can inspect the compiled edges directly:

```sh
.lake/build/bin/proof-pairs examples/tiny/.lake/build/lib/lean/Main.olean --edges
```

For a larger checkout, build or restore its matching `.olean`, private module data, and `.ilean` files first. Pass `--root` once per theorem and `--root-module` for their common importing module. The source directory defaults to `src`. Each run writes to a new output directory. The compressed JSONL graph retains the declaration, its owning project module, and its direct dependencies. In the report, `outside_roots` includes theorems with a recognized source header and compiler range. A missing range leaves that theorem outside the source-level inventory.

In this example the typed scanner reports `same-statement`: the second proof introduces a local binding, so the two proofs have different stored bodies. Compare them with:

```sh
.lake/build/bin/proof-pairs examples/tiny/.lake/build/lib/lean/Demo/Left.olean \
  examples/tiny/.lake/build/lib/lean/Demo/Right.olean
```

On the [RH m41 revision](https://github.com/leanprover-community/riemann-hypothesis/tree/5cbb17ac392eed2932c2d29cb78c49112895a11d), the public workflow scanned 801 project modules and traced 49,293 declarations from five roots. Its gapped search screened 14,447 located tactic proofs, seeded 2,420 pairs, and nominated 163 for further inspection. Those numbers describe the search space and its output. Each proposed merge still needs verification.

## Why search from coarse to fine?

Suppose a 300-line construction is absent from every selected proof. Factoring three lines out of each of its lemmas first would create work that disappears when the construction is removed. Conversely, two essential proofs may each spend 30 lines constructing the same object. A reachability pass keeps both proofs, but comparing their intermediate conclusions can expose the shared construction.

| Order | What the optimizer looks for | What decides the next step |
| --- | --- | --- |
| 1. Modules and declaration families | Start at the named roots and follow constants in each declaration's type and value. Group disconnected imports and look for declarations used only inside a candidate family. | Check incoming references from retained declarations, source-level commands, registrations, and public interfaces. A lemma can be useful independently of the chosen theorem. |
| 2. Whole proofs | Bucket candidates by statement and proof fingerprints. Resolve names against compiler metadata and compare normalized terms inside a bucket. | The comparison retains binder kinds, dependencies, and argument order. Equal statements may have quite different derivations. A path from the same root to both occurrences establishes where sharing would matter. |
| 3. Shared intermediate derivations | Search for repeated runs of source lines and typed subterms. Work backward from a common conclusion. When the proof below a premise differs, try passing that premise as a lemma argument. | Check that the arguments are in scope at both calls and that the helper is visible through the imports. Count the helper, its arguments, and every replacement. Repeated tactic text alone is only a lead. |
| 4. Local bindings and steps | On the surviving source, look for unused local facts, duplicate hypotheses, forwarding lemmas, and administrative equality steps. | Check elaborated uses, including implicit arguments and instances. Revisit these sites after settling an enclosing change so the same savings are counted once. |

Within each level, prefer the largest credible **net** saving. A useful extraction can grow temporarily while the new lemma and old proofs coexist. Evaluate the complete patch. Source lines and bytes describe the human-facing change. The union of distinct expressions across affected proof bodies measures structural sharing and can move differently. Record the modules and roots used for a measurement. A local reduction by itself gives no timing result or whole-library size bound.

### Search, rewriting, and validation

- **Find candidates cheaply.** The declaration census caches compiled artifacts by content. Contiguous duplicate search uses a rolling fingerprint and a rightmost minimum in each window. The gapped search separately uses lines specific to a pair of reachable proofs to seed a sequence comparison. It can find two matching runs on opposite sides of a different intermediate step. Both prefilters have limited recall. [Census](tools/census.py) · [Contiguous runs](tools/long_duplicates.py) · [Gapped runs](tools/gapped_runs.py)
- **Verify the boundary.** The linked graph follows references in the imported Lean environment. The source index additionally resolves named uses, including uses that disappear during elaboration. Compute both witnesses for a proposed same-root extraction. Check retained interfaces and registrations separately before deleting anything. [Linked roots](tools/LinkedRoots.lean) · [Root witnesses](tools/root_paths.py) · [Exclusive families](tools/unreferenced_family.py)
- **Try a replacement at its original sites.** The extractor closes a local conclusion over its dependencies, places a helper where its callers can see it, and compiles edited modules in an isolated directory. The strict replay path unfolds the new helper and permitted auxiliaries, reduces administrative applications and lets, and compares the resulting expressions against the originals. It emits an accepted patch only after the whole change reduces source lines, bytes, and the measured proof DAG. More ambitious mathematical rewrites can pass Lean and preserve the argument without satisfying strict replay; report their evidence separately. [Source extractor](tools/share_construction.py) · [Compiled comparison and replay](tools/ProofPairs.lean) · [Parameterized subterm search](tools/ReverseShare.lean)
- **Check the contribution against its destination.** Start with the current upstream default branch. Inspect the actual diffs of open PRs and pending merge batches for overlap. Batch related edits and locally build the affected modules. Read the finished mathematical argument before submitting it. A shorter proof that hides a useful construction or removes a useful independent lemma can be a poor contribution. Upstream CI and maintainer review remain part of the target project's process.

For an extraction experiment, run from the **target project's** directory, using its source, matching compiled library and Lake environment. Set `FLOW` to the optimizer checkout and provide the candidate modules in import order:

```sh
lake env python3 "$FLOW/tools/share_construction.py" src .lake/build/lib/lean \
  .flow/extraction MyProject.Provider MyProject.Consumer --helper MyProject.sharedStep
```

Pass each project-specific Lean option with a repeated `--lean-arg=...` so compilation uses the same settings as the baseline. The output directory must be new. An experiment can finish with no accepted patch. Inspect its trial results to distinguish a source-size rejection, an unavailable premise, and a failed replay. To see a provably canonical fragment, run `lake env lean theory/EqualityCleanup.lean` in this repository. For labelled equality certificates with fixed endpoints, four rules remove left and right reflexivity units, double symmetry, and symmetry of reflexivity. The Lean development proves that the normal form is reachable and minimizes constructor count in its rule-generated equivalence class. It also gives two distinct terminal results for a different pair of rules. The general RH optimizer makes no global minimality claim. [Checked development](theory/EqualityCleanup.lean)

To inspect possible upstream overlap, run the read-only command below with GitHub CLI access. The report includes same-file diffs for manual comparison. Recheck the default-branch head before pushing.

```sh
python3 tools/upstream.py OWNER/REPO src/MyProject/Provider.lean --author GITHUB_LOGIN
```

### Reuse an existing proof at a selected cut

Choose a complete tactic block inside a surviving declaration. At that location, the local hypotheses, instances and imports determine which providers Lean can actually use. The following command tries instance synthesis and then Lean’s library search. It compiles the module again with the explicit suggestion in place of the original block. On the example it replaces four tactic lines with `exact ⟨hp, hq⟩`, saving three lines and 50 UTF-8 bytes.

```sh
python3 tools/provider_site.py examples/tiny Demo.Right examples/tiny/src/Demo/Right.lean 8 11
```

The range is inclusive. Use `--term` for a complete term on separate lines after `:=`, and pass the project's Lean options with `--lean-arg`. A replayed suggestion has a checked call site. A claim that two proofs share the same derivation still requires structural comparison. Before proposing the change, read the diff and measure the affected reachable proof bodies. After a miss, search the documentation of the imported modules using the mathematical names of the construction. A name found in a docstring is a lead to try at the original site. [Provider probe](tools/provider_site.py) · [Result-symbol search](tools/result_providers.py)

A retrospective check at the original first proper-action binding in RH #7797 recovered `inferInstance` and replayed the surrounding module, saving seven lines and 520 bytes in that block. The experiment supplied the site. On RH m42b the same library-search strategy failed to close the 25-line Schur monomial surjectivity argument and the 21-line openness argument in the global norm theorem. Both contain substantive intermediate constructions. [Merged coset-integral proof](https://github.com/leanprover-community/riemann-hypothesis/pull/7797/files) · [Schur matrix proof](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/Lib/GLn/SchurModule/SchurMatrix.lean#L921-L946) · [Global norm proof](https://github.com/leanprover-community/riemann-hypothesis/blob/61d870d08d5f6f5cc12f31fe40f5689024ea15ab/src/Lib/ClassField/Global/NormTheorems.lean#L194-L215)

For a local binding whose source extent is ambiguous, the cascade can ask Lean for tactic ranges and the goals before and after a tactic in the selected declaration. It then removes only the binding, preserving a sibling tactic after a semicolon. The strict checker still recompiles the module and compares the resulting proof term. On RH, removing `hrow` from a line shared with `hcol` made a later `lia` fail. The original proof was kept. [Tactic spans](tools/TacticSpans.lean) · [Local cascade](tools/local_cascade.py)

After a larger rewrite, pass `--before PREVIOUS_REPORT_DIRECTORY` to the workflow with the same roots. The `newly_outside_roots` list contains each former owner and name once. Use it on corresponding before/after builds, then check surviving callers and registrations before considering deletion. Independent candidates can run in separate temporary directories with the same imported build products. Compile modules that depend on one another in import order.

For a batch of proposed binding deletions, `check_local_haves.py --jobs N` groups all sites in a module into one scanner call, unpacks the matching artifacts in parallel, and writes the results in a stable order. On 15 newly nominated sites across 12 RH m42b modules, the one-worker and twelve-worker reports were byte-identical. All 15 bindings had a compiled use. Independent module checks can share the same read-only artifact cache and keep temporary products separate. [Batch checker](tools/check_local_haves.py)

A separate m42b application replaced a seven-line derivation of measurable multiplication on the Bessel graph with a single instance binding. This removed six lines and 445 bytes. The affected module’s 42 reachable proof bodies used 37,354 distinct expression nodes before the change and 37,105 after it. The target declaration used 5,256 and 4,086 elaboration heartbeats respectively. This is a module-local measurement. [RH application #8074](https://github.com/leanprover-community/riemann-hypothesis/pull/8074)

### Running the RH workflow across two machines

1. **Pin the inputs.** Read the official default branch and commit from GitHub. Use the same source revision, Lean build inputs and optimizer revision on both workers. Review open PRs and merge batches for edits to the proposed proof. Repeat the overlap check if the upstream head changes. [Upstream comparison](tools/upstream.py)
2. **Choose the next proof.** After checking whole families for removal, start at the final Lean goal of a surviving long derivation. Try an existing lemma at that site under its actual imports and local hypotheses. Cross-file matches on the result symbol or rare shared dependencies can suggest a lemma already used indirectly. If two proofs have different premises but appear to share their remaining steps, test that specific suffix with `share_construction.py --suffix-group`. Count the new lemma and the changes at every caller. [Provider replay](tools/provider_site.py) · [Suffix extraction](tools/share_construction.py)
3. **Divide independent work.** One machine coordinates candidates and upstream checks. Both compile disjoint candidate batches using separate output directories and compatible read-only build products. A free worker can take the next ready module. Compile a changed provider before its callers, then measure their combined reachable proof bodies. The five-minute RH check-in collects finished work, checks for author requests and replenishes the queue. The check-in and worker dispatch are configured by the operator. [Compilation overlay](tools/module_overlay.py) · [Root paths](tools/root_paths.py)
4. **Submit a complete change.** Review the mathematical argument and the net change in source and proof bodies. Run the upstream author checks on the finished patch. RH currently asks authors to run `lake exe cache get` followed by `lake build` before opening a PR. Hosted CI, reviewer approval and merging run upstream. Track requests on the current PR head so a queued check or a superseded change does not trigger duplicate work. [RH contribution instructions](https://github.com/leanprover-community/riemann-hypothesis/blob/main/AGENTS.md)

## Optional LLM interface

Use a model when the open question is mathematical. For example, do two constructions share a useful invariant, which hypothesis should become an argument, or would the proposed helper make the proof harder to follow? The interface sends one selected candidate through standard input and returns the reviewer's text on standard output. The packet contains theorem names, common roots, and matched line ranges. The optional `--source` flag includes the source between the first and last match on each side.

```sh
# Inspect the exact packet locally.
python3 tools/review.py .flow/tiny/report.json 0 --source examples/tiny/src

# Exercise the adapter contract locally by echoing the packet.
python3 tools/review.py .flow/tiny/report.json 0 --command cat

# Example with a separately installed and configured Claude CLI.
python3 tools/review.py .flow/tiny/report.json 0 --source examples/tiny/src \
  --command claude -p --output-format text --tools "" --no-session-persistence
```

A provider wrapper can use the same contract. Model output is advisory text. A proposed rewrite still goes through local Lean checks and the same size accounting. Use the packet preview to see what you would share with a provider. [Adapter](tools/review.py)

## Bibliography and connections to the implementation

1. **Backward trimming.** Marijn J. H. Heule, Warren A. Hunt Jr., and Nathan Wetzler, *Trimming while Checking Clausal Proofs*, FMCAD 2013, §IV. Their checker starts at the empty clause and marks premises needed to justify it. Our analogous question is which declarations a fixed Lean theorem actually uses. Lean provides elaborated type and value references, while clausal trimming reconstructs reasons by unit propagation. [Paper](https://www.cs.cmu.edu/~mheule/publications/druptrim.pdf)
2. **Finding partial copies.** Saul Schleimer, Daniel S. Wilkerson, and Alex Aiken, *Winnowing: Local Algorithms for Document Fingerprinting*, SIGMOD 2003, Definition 1. Our contiguous-run scanner uses their rightmost-minimum selection rule on sequences of source-line identifiers. Mathematical equivalence and the recall of our complete pipeline require separate evidence. [Paper](https://theory.stanford.edu/~aiken/publications/papers/sigmod03.pdf)
3. **Sharing proof DAGs.** Simone Fulvio Rollini, Roberto Bruttomesso, Natasha Sharygina, and Aliaksei Tsitovich, *Resolution Proof Transformation for Compression and Interpolation*, Algorithms 8–9. They merge resolution nodes with identical parents and show how transformations can expose further sharing. Our typed comparison must also account for Lean binders, universes, and proof bodies. Coarse-to-fine scheduling here is an engineering choice, with no imported optimality guarantee. [Paper](https://arxiv.org/pdf/1307.2028)
4. **Parameterizing the differences.** Frank Pfenning, *Unification and Anti-Unification in the Calculus of Constructions*, LICS 1991. A least general generalization can describe what two proofs share in the paper's higher-order pattern fragment. Our extractor searches a restricted set of local constructions and tests the proposed parameters at the call sites. It does not compute a general higher-order anti-unifier. [Paper](https://www.cs.cmu.edu/~fp/papers/lics91.pdf)
5. **The scope of a canonical form.** Aaron Stump and Li-Yang Tan, *The Algebra of Equality Proofs*, RTA 2005, study a restricted equality-proof algebra and the role of independent assumptions. Arthur F. Ramos, Ruy J. G. B. de Queiroz, and Anjolina G. de Oliveira, *On the Identity Type as the Type of Computational Paths*, §4, give explicit reductions involving symmetry, transitivity, and reflexivity. These are precedents for stating the generators and the cost model when claiming a canonical result. [Stump and Tan](https://cshub.bc.edu/stumpaa/papers/rta05.pdf) · [Ramos et al.](https://arxiv.org/pdf/1504.04759)
6. **Checking proposals.** Leonardo de Moura and Sebastian Ullrich, *The Lean 4 Theorem Prover and Programming Language*, CADE 2021. Lean's elaborator and kernel let a search procedure propose a readable replacement and have Lean check its type. Flow adds the separate structural comparison and net-size measurements described above. [Paper](https://lean-lang.org/papers/lean4.pdf)

7. **Tactic-state pruning and replay.** Daniel Selsam’s Lean 3 cleaner in OpenAI’s lean-gym tracks the continuation goals when deleting a tactic region. Meta’s Evariste documents how a hypothesis can guide later tactics even when it disappears from the final term. Flow uses Lean 4 tactic information and its own replay implementation. [lean-gym source](https://github.com/openai/lean-gym/blob/1585ac4d2e56a1ceb72243ce859645b9d0069d34/src/tools/shrink_proof.lean) · [Evariste source](https://github.com/facebookresearch/Evariste/blob/ef43511f2d234bcb28e380388b8fe0d06a4d93a7/formal/runtime_loaded_lean_files/cleaning_utils/v1/useless_tactics_removal.lean)
8. **Dependency restructuring and retrieval.** The LeanLean study of 64 repositories distinguishes source compression from elaboration cost. Anthropic’s FLT report describes the Columbia team’s Prove2Me interface for navigating statements and their descriptions. Flow uses documentation for discovery and Lean’s own library search to test a candidate in context. [LeanLean](https://www.sri.inf.ethz.ch/publications/rognvaldsson2026leanlean) · [FLT report](https://www.anthropic.com/research/formalizing-fermats-last-theorem) · [Lean library search](https://github.com/leanprover/lean4/blob/v4.37.0-rc1/src/Lean/Meta/Tactic/LibrarySearch.lean)

## Accepted applications in the Riemann Hypothesis project

Four examples show why the useful unit of work varies. Removing an unused Fock pairing block saved **372 source lines** while retaining the public theorem. In partial Hecke duality, applying the forward implication twice with swapped indices and the dual-lattice involution removed the separate converse calculation. In the Hodge–Tate cup projections, two results share the same objectwise splitting. The Fock vacuum refactor provides an example with structural replay: specializing a single proof at both call sites removed 82 source lines and reduced the union of the two measured proof bodies from 32,151 to 24,207 expression nodes. [#1337](https://github.com/leanprover-community/riemann-hypothesis/pull/1337) · [#7344](https://github.com/leanprover-community/riemann-hypothesis/pull/7344) · [#7709](https://github.com/leanprover-community/riemann-hypothesis/pull/7709) · [#4575](https://github.com/leanprover-community/riemann-hypothesis/pull/4575)

As of November 27, 2026, GitHub records **128 merged upstream PRs** from this workflow. We checked their merge commits against both histories. The earlier default-branch history is now preserved on `alpoge`, so the base label displayed by GitHub alone would give a misleading breakdown. These are tool-assisted contributions across successive versions. The list includes proposals that needed mathematical review or an individually written replacement.

<details>
<summary>Current main history · 65 merged PRs</summary>

| PR | Accepted change |
| --- | --- |
| [#5628](https://github.com/leanprover-community/riemann-hypothesis/pull/5628) | Infer the step function properties in TopFloor |
| [#5650](https://github.com/leanprover-community/riemann-hypothesis/pull/5650) | Remove unused steps from the Eigenspace proofs |
| [#5658](https://github.com/leanprover-community/riemann-hypothesis/pull/5658) | Reuse the reduction of a matrix at a split place |
| [#5662](https://github.com/leanprover-community/riemann-hypothesis/pull/5662) | Use the transposed lift definition in the first path |
| [#5962](https://github.com/leanprover-community/riemann-hypothesis/pull/5962) | Share the monic integrality argument in CrystallineRings |
| [#6086](https://github.com/leanprover-community/riemann-hypothesis/pull/6086) | Remove the unused proof of discreteness for quotient modules |
| [#6183](https://github.com/leanprover-community/riemann-hypothesis/pull/6183) | Share the generator induction for the exterior algebra functor |
| [#6249](https://github.com/leanprover-community/riemann-hypothesis/pull/6249) | Use the Bessel stabilizer factor directly in the frame proofs |
| [#6287](https://github.com/leanprover-community/riemann-hypothesis/pull/6287) | Reuse Ext naturality in long exact sequence comparisons |
| [#6339](https://github.com/leanprover-community/riemann-hypothesis/pull/6339) | Derive the raising and lowering coefficient identities together |
| [#6368](https://github.com/leanprover-community/riemann-hypothesis/pull/6368) | Deduce right-block unitary membership by swapping the summands |
| [#6404](https://github.com/leanprover-community/riemann-hypothesis/pull/6404) | Share the plane descent argument for the two cone integrals |
| [#6446](https://github.com/leanprover-community/riemann-hypothesis/pull/6446) | Share the point mass factorization for block kernels |
| [#6470](https://github.com/leanprover-community/riemann-hypothesis/pull/6470) | Share the support argument for nonzero frame pivots |
| [#6504](https://github.com/leanprover-community/riemann-hypothesis/pull/6504) | Reuse the inverse law for the hyperbolic frame matrices |
| [#6513](https://github.com/leanprover-community/riemann-hypothesis/pull/6513) | Reuse continuity of characteristic polynomial coefficients |
| [#6543](https://github.com/leanprover-community/riemann-hypothesis/pull/6543) | Use the star involution for the reverse Weyl matrix product |
| [#6638](https://github.com/leanprover-community/riemann-hypothesis/pull/6638) | Share nonvanishing of the denominator in the holomorphic minor formulas |
| [#6649](https://github.com/leanprover-community/riemann-hypothesis/pull/6649) | Share the pole bound for deep points in the cup coboundary proofs |
| [#6701](https://github.com/leanprover-community/riemann-hypothesis/pull/6701) | Reuse coefficient-map powers in the polynomial twisted norm |
| [#6716](https://github.com/leanprover-community/riemann-hypothesis/pull/6716) | Use the Levi action on frames in the two rank-one scaling identities |
| [#6775](https://github.com/leanprover-community/riemann-hypothesis/pull/6775) | Reuse the target-parameter gap on both sides of a grid centre |
| [#6796](https://github.com/leanprover-community/riemann-hypothesis/pull/6796) | Deduce the multinomial exponent bound from the defect threshold estimate |
| [#6825](https://github.com/leanprover-community/riemann-hypothesis/pull/6825) | Apply the square laws directly to the expanded triangle lifts |
| [#6896](https://github.com/leanprover-community/riemann-hypothesis/pull/6896) | Derive deep points for nonpositive jumps from the gap lemma |
| [#6912](https://github.com/leanprover-community/riemann-hypothesis/pull/6912) | Share the conjugate tame generator in split-prime reciprocity |
| [#6923](https://github.com/leanprover-community/riemann-hypothesis/pull/6923) | Share the monomial lowering identity across lift-ideal levels |
| [#7038](https://github.com/leanprover-community/riemann-hypothesis/pull/7038) | Share the basis-entry form of the survival identity |
| [#7056](https://github.com/leanprover-community/riemann-hypothesis/pull/7056) | Share the archimedean estimate for frame indices |
| [#7068](https://github.com/leanprover-community/riemann-hypothesis/pull/7068) | Apply the four-block pairing formula in the class sum |
| [#7083](https://github.com/leanprover-community/riemann-hypothesis/pull/7083) | Share basis coordinates in the two theta decay bounds |
| [#7145](https://github.com/leanprover-community/riemann-hypothesis/pull/7145) | Share the generator formulas for the perfect-line projection |
| [#7185](https://github.com/leanprover-community/riemann-hypothesis/pull/7185) | Share the coefficient scaling calculation in Hecke transfer |
| [#7251](https://github.com/leanprover-community/riemann-hypothesis/pull/7251) | Use adelic unfolding directly after factoring the tent integrand |
| [#7274](https://github.com/leanprover-community/riemann-hypothesis/pull/7274) | Use the explicit integral representative in the trace limit proof |
| [#7311](https://github.com/leanprover-community/riemann-hypothesis/pull/7311) | Give the monomial exponent map explicitly for one-row Schur matrices |
| [#7325](https://github.com/leanprover-community/riemann-hypothesis/pull/7325) | Specialize the split basis to one hyperbolic pair |
| [#7344](https://github.com/leanprover-community/riemann-hypothesis/pull/7344) | Use involutivity for the converse in partial Hecke duality |
| [#7377](https://github.com/leanprover-community/riemann-hypothesis/pull/7377) | Share the matrix products for opposite line shifts |
| [#7409](https://github.com/leanprover-community/riemann-hypothesis/pull/7409) | Simplify the rank calculations in hyperbolic plane descent |
| [#7479](https://github.com/leanprover-community/riemann-hypothesis/pull/7479) | Share the scaled discriminant bound for near pairs |
| [#7519](https://github.com/leanprover-community/riemann-hypothesis/pull/7519) | Use the individual Galois restriction lemmas at single-result callers |
| [#7544](https://github.com/leanprover-community/riemann-hypothesis/pull/7544) | Share the level-zero step calculation for deep points |
| [#7563](https://github.com/leanprover-community/riemann-hypothesis/pull/7563) | Remove the unused reflection identity for the matrix logarithm integrand |
| [#7622](https://github.com/leanprover-community/riemann-hypothesis/pull/7622) | Use the Bessel frame-column criterion for the simple-root sum |
| [#7640](https://github.com/leanprover-community/riemann-hypothesis/pull/7640) | Read the Bessel frame coefficients directly from the isotropic rows |
| [#7690](https://github.com/leanprover-community/riemann-hypothesis/pull/7690) | Share the monic residue evaluation for opposite nodes |
| [#7709](https://github.com/leanprover-community/riemann-hypothesis/pull/7709) | Share the objectwise splitting in the two Hodge–Tate cup projections |
| [#7752](https://github.com/leanprover-community/riemann-hypothesis/pull/7752) | Use the open character kernel in the local norm criterion |
| [#7797](https://github.com/leanprover-community/riemann-hypothesis/pull/7797) | Reuse the proper-action instances in the coset integral |
| [#7826](https://github.com/leanprover-community/riemann-hypothesis/pull/7826) | Use the zero-section retraction and functoriality of evaluation |
| [#7899](https://github.com/leanprover-community/riemann-hypothesis/pull/7899) | Share the pair-indexed sum estimate for remaining terms |
| [#8074](https://github.com/leanprover-community/riemann-hypothesis/pull/8074) | Use measurable multiplication on the Bessel graph in the integral |
| [#8132](https://github.com/leanprover-community/riemann-hypothesis/pull/8132) | Share the middle and reversed-index facts for string frames |
| [#8210](https://github.com/leanprover-community/riemann-hypothesis/pull/8210) | Share the entrywise second-moment calculation |
| [#8218](https://github.com/leanprover-community/riemann-hypothesis/pull/8218) | Share the block-column identity for the position stabilizer |
| [#8233](https://github.com/leanprover-community/riemann-hypothesis/pull/8233) | Share the dot-product calculation for congruent frame lifts |
| [#8254](https://github.com/leanprover-community/riemann-hypothesis/pull/8254) | Compute the Bessel graph action on the definite frame |
| [#8313](https://github.com/leanprover-community/riemann-hypothesis/pull/8313) | Apply the Rallis kernel criterion directly to the single lift |
| [#8330](https://github.com/leanprover-community/riemann-hypothesis/pull/8330) | Use the radical parameter directly in splitting projector recovery |
| [#8344](https://github.com/leanprover-community/riemann-hypothesis/pull/8344) | Evaluate the diagonal determinant in partial Hecke duality |
| [#8346](https://github.com/leanprover-community/riemann-hypothesis/pull/8346) | Share the finite-place integrality argument for hermitian pairings |
| [#8386](https://github.com/leanprover-community/riemann-hypothesis/pull/8386) | Share the sign-case calculation in the Frobenius cycle root lemma |
| [#8408](https://github.com/leanprover-community/riemann-hypothesis/pull/8408) | refactor(Lib/PadicComparison/HodgeTate): share the Yoneda composition step |
| [#8682](https://github.com/leanprover-community/riemann-hypothesis/pull/8682) | Share the integral factorization for orthogonal sums in the model inner product and the Weil action |

</details>

<details>
<summary>Earlier history preserved on alpoge · 63 merged PRs</summary>

| PR | Accepted change |
| --- | --- |
| [#1327](https://github.com/leanprover-community/riemann-hypothesis/pull/1327) | Reuse the wave-grid bound on the sum of absolute weights |
| [#1337](https://github.com/leanprover-community/riemann-hypothesis/pull/1337) | Remove the unused Fock block pairing proofs |
| [#1407](https://github.com/leanprover-community/riemann-hypothesis/pull/1407) | Share the theta reading and orthogonality proofs |
| [#1420](https://github.com/leanprover-community/riemann-hypothesis/pull/1420) | Remove unused divided-power augmentation lemmas |
| [#1424](https://github.com/leanprover-community/riemann-hypothesis/pull/1424) | Remove unused adic approximation lemmas |
| [#1430](https://github.com/leanprover-community/riemann-hypothesis/pull/1430) | Remove unused mixed discriminant expansion lemmas |
| [#1487](https://github.com/leanprover-community/riemann-hypothesis/pull/1487) | Share tensor factorization helpers with the eigenspace bound |
| [#1499](https://github.com/leanprover-community/riemann-hypothesis/pull/1499) | Share level operator proofs in the dense threshold cases |
| [#1519](https://github.com/leanprover-community/riemann-hypothesis/pull/1519) | Share the five theta identities in the divisor proofs |
| [#1542](https://github.com/leanprover-community/riemann-hypothesis/pull/1542) | Reuse the Hecke and level trace lemmas in the integrability argument |
| [#1555](https://github.com/leanprover-community/riemann-hypothesis/pull/1555) | Reuse the local span criterion for full lattices |
| [#1643](https://github.com/leanprover-community/riemann-hypothesis/pull/1643) | Share the descent and direct sum proofs for Galois representations |
| [#1677](https://github.com/leanprover-community/riemann-hypothesis/pull/1677) | Remove unused bounds in the divisibility proofs |
| [#1683](https://github.com/leanprover-community/riemann-hypothesis/pull/1683) | Remove unused local facts from the Hermitian curvature proofs |
| [#1690](https://github.com/leanprover-community/riemann-hypothesis/pull/1690) | Remove repeated theta-function closure proofs |
| [#1696](https://github.com/leanprover-community/riemann-hypothesis/pull/1696) | Remove the unused top-level cut germ proof and its helper |
| [#1704](https://github.com/leanprover-community/riemann-hypothesis/pull/1704) | Remove unused local facts from the global interpolation proofs |
| [#1708](https://github.com/leanprover-community/riemann-hypothesis/pull/1708) | Remove the unused cut germ mean proof and its local lemmas |
| [#1712](https://github.com/leanprover-community/riemann-hypothesis/pull/1712) | Remove the unused cover elements existence proof and its auxiliary lemmas |
| [#1776](https://github.com/leanprover-community/riemann-hypothesis/pull/1776) | Remove the unused divisor basis existence proof and its auxiliary lemmas |
| [#1791](https://github.com/leanprover-community/riemann-hypothesis/pull/1791) | Remove the unused finite determinant order proof and its auxiliary lemmas |
| [#1804](https://github.com/leanprover-community/riemann-hypothesis/pull/1804) | Use the existing full-lattice lemma for self-dual lattices |
| [#1816](https://github.com/leanprover-community/riemann-hypothesis/pull/1816) | Remove unused proofs in EntAtD |
| [#1837](https://github.com/leanprover-community/riemann-hypothesis/pull/1837) | Remove unused proofs in WAKummerEps |
| [#1843](https://github.com/leanprover-community/riemann-hypothesis/pull/1843) | Reuse the addition and scalar multiplication lemmas for theta functions |
| [#1871](https://github.com/leanprover-community/riemann-hypothesis/pull/1871) | Remove unused proofs in InvMulMemIntegralGLOfMem |
| [#1927](https://github.com/leanprover-community/riemann-hypothesis/pull/1927) | Share the parabolic matrix construction in the theta lift proofs |
| [#2178](https://github.com/leanprover-community/riemann-hypothesis/pull/2178) | Remove unused proofs in CrystallineDeRham |
| [#2184](https://github.com/leanprover-community/riemann-hypothesis/pull/2184) | Reuse the local-field absolute value formula |
| [#2208](https://github.com/leanprover-community/riemann-hypothesis/pull/2208) | Share finite-dimensional orbit constructions |
| [#2220](https://github.com/leanprover-community/riemann-hypothesis/pull/2220) | Remove unused proofs in CellConv |
| [#2222](https://github.com/leanprover-community/riemann-hypothesis/pull/2222) | Reuse closure of oriented theta functions |
| [#2228](https://github.com/leanprover-community/riemann-hypothesis/pull/2228) | Remove unused twisted theta translation proofs |
| [#2264](https://github.com/leanprover-community/riemann-hypothesis/pull/2264) | Remove unused invariant vector field lemmas |
| [#2346](https://github.com/leanprover-community/riemann-hypothesis/pull/2346) | Share continuity of the differentiated Bessel integrand |
| [#2373](https://github.com/leanprover-community/riemann-hypothesis/pull/2373) | Remove unused Fock bottom-weight lemmas |
| [#2399](https://github.com/leanprover-community/riemann-hypothesis/pull/2399) | Remove unused central shift lemmas |
| [#2413](https://github.com/leanprover-community/riemann-hypothesis/pull/2413) | Remove unused determinant expansion lemmas |
| [#2422](https://github.com/leanprover-community/riemann-hypothesis/pull/2422) | Remove unused level-cover chart proofs |
| [#2868](https://github.com/leanprover-community/riemann-hypothesis/pull/2868) | Remove unused lattice covolume lemmas |
| [#2889](https://github.com/leanprover-community/riemann-hypothesis/pull/2889) | Remove unused definite unitary Casimir lemmas |
| [#3024](https://github.com/leanprover-community/riemann-hypothesis/pull/3024) | Remove unused lemmas on Lagrangian frames |
| [#3031](https://github.com/leanprover-community/riemann-hypothesis/pull/3031) | Remove unused local hypotheses in sharp restriction proofs |
| [#3227](https://github.com/leanprover-community/riemann-hypothesis/pull/3227) | Remove unused standard lattice covolume lemmas |
| [#3242](https://github.com/leanprover-community/riemann-hypothesis/pull/3242) | Share the Dirac inequality proof for the two core modules |
| [#3292](https://github.com/leanprover-community/riemann-hypothesis/pull/3292) | Share the lattice argument in the moved datum step |
| [#3671](https://github.com/leanprover-community/riemann-hypothesis/pull/3671) | Share the construction of pullback SAB map data |
| [#3683](https://github.com/leanprover-community/riemann-hypothesis/pull/3683) | Remove unused embedding and intersection proofs |
| [#3701](https://github.com/leanprover-community/riemann-hypothesis/pull/3701) | Remove unused small section count lemmas |
| [#3724](https://github.com/leanprover-community/riemann-hypothesis/pull/3724) | Remove unused twist intersection lemmas |
| [#3741](https://github.com/leanprover-community/riemann-hypothesis/pull/3741) | Remove unused finite fibre lemmas |
| [#3961](https://github.com/leanprover-community/riemann-hypothesis/pull/3961) | Remove six unused ConvGrp lemmas |
| [#3993](https://github.com/leanprover-community/riemann-hypothesis/pull/3993) | Remove unused continuous evaluation lemmas |
| [#4001](https://github.com/leanprover-community/riemann-hypothesis/pull/4001) | Remove unused auxiliary reciprocity lemmas |
| [#4082](https://github.com/leanprover-community/riemann-hypothesis/pull/4082) | Remove unused norm compatibility lemmas |
| [#4116](https://github.com/leanprover-community/riemann-hypothesis/pull/4116) | Remove unused Hecke sum lemmas |
| [#4140](https://github.com/leanprover-community/riemann-hypothesis/pull/4140) | Remove unused chart constants and their proposition |
| [#4151](https://github.com/leanprover-community/riemann-hypothesis/pull/4151) | Remove unused big cell lemmas |
| [#4218](https://github.com/leanprover-community/riemann-hypothesis/pull/4218) | Share the segment-block weight proof |
| [#4283](https://github.com/leanprover-community/riemann-hypothesis/pull/4283) | Remove unused balanced projective rank lemmas |
| [#4307](https://github.com/leanprover-community/riemann-hypothesis/pull/4307) | Remove the unused Levi functional equation lemma |
| [#4575](https://github.com/leanprover-community/riemann-hypothesis/pull/4575) | Share the Fock vacuum entire-function proof |
| [#4697](https://github.com/leanprover-community/riemann-hypothesis/pull/4697) | Remove the unused Kummer epsilon module |

</details>
