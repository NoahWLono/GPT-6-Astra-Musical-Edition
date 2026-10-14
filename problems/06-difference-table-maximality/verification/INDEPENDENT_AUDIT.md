INDEPENDENT AUDIT: DIFFERENCE-TABLE MAXIMALITY
14 October 2026

VERDICT
The frozen proof package passes an independent source rebuild. It establishes 22 explicit, nonempty, pairwise distinct TableHolds loci, each maximal among all 10! edge-permutation loci in its own fixed canonical chamber. It does not establish that every maximal locus appears among these 22. This is a verified structural partial result, not a solution of Problem 5.1.

FROZEN BUILD AND TRUST
The input was the 20 sources identified in the source hash inventory, copied before building, with every source SHA-256 checked. All 20 compiled successfully with Lean 4.32.2 and mathlib revision 905b95818eb32af7874a58b427f50c1711a5e96c. The isolated Lean search path used the new snapshot plus upstream mathlib/package caches; no project .olean files were reused. Upstream Lean/mathlib binaries were reused rather than independently bootstrapped.

The original proof sources contain no custom axioms, proof placeholders, or native-decision shortcuts. The final certificates use decide +kernel. Transitive axiom exports for the 22 maximality results and pairwise-distinctness result contain only propext, Classical.choice, and Quot.sound. The general matching criterion needs only Quot.sound in its reported export. The source-only replay and the recorded export summary establish these checks.

An additional audit-only AuditAggregate.lean compiled successfully. Its all_maximal theorem links the exact 22 maps appearing in DistinctMaximal22 to their corresponding maximality theorems, eliminating a possible packaging mismatch. It also proves maps_bijective and all_nonempty for those exact maps. ExportAudit.lean checks the theorem signatures and transitive axioms. These two files do not alter the original 20-source package. The 22-file build_manifest.json records their hashes and build order. rebuild.py rebuilds the package in a new output directory.

WHAT THE PROOFS SAY
For fixed p,q, write S_pi for TableHolds p q pi. Every competing sigma is an arbitrary equivalence Fin 10 ≃ Fin 10, not a member of a preselected list. The aggregate theorem proves S_pi ⊆ S_sigma implies S_sigma ⊆ S_pi for each of the 22 representatives. The distinctness theorem gives, for every ordered pair of distinct indices i,j, a real point belonging to S_i but not S_j. Thus both nonemptiness and distinction are genuine statements about real loci, not unequal matrices or filenames.

The eleven collision-free representatives A1–A3, D1–D4, and F1–F4 satisfy the stronger conclusion sigma = pi whenever S_pi ⊆ S_sigma. Here “collision-free” means no two distinct source-distance functions agree throughout the locus; individual sample points can still contain repeated distances. It does not mean the locus is a geometric singleton.

THE STRUCTURAL REDUCTION
CollisionDomination proves, for arbitrary sets of labels and values and any common chamber C, that inclusion of matching loci is equivalent to all source pairs a and sigma(pi^{-1}(a)) agreeing throughout S_pi. This uses no convexity, rank assumption, or finite classification.

SampleCollisionCertificate uses rational feasible samples to bound those forced equalities: if two labels differ on a sample, they cannot be forced to agree everywhere. No assertion that the samples span the entire affine hull is needed. BlockMaximality reconstructs any possible dominator as pi followed by permutations within the resulting blocks. CompactMaximalityCertificate then proves reverse inclusion for every such fiber permutation by exact row combinations and, where necessary, a positive opposed pair of nonnegative chamber heads.

The finite candidate counts are 1 for each of the eleven collision-free representatives; 2 for each G1–G4; 8 for each B1–B5; 32 for B6; and 6 for C. Their total is 97. The largest reduction has five two-element blocks, giving 2^5 = 32 permutations. The bound is on fiber-permutation choices, not on the number of edges in a block. The generated universal valid theorem kernel-checks every choice. Eight B6 certificates use a nonzero boundary-forcing pair; all other compact reverse certificates use matching-row combinations alone.

These proofs do not import the 297-case reflected affine-hull certificates. The earlier Python search can supply candidates and numbers without becoming a logical assumption in this proof package. Discovery can rely on prior finite work even though verification does not assume its completeness.

SEMANTIC CHECK AGAINST THE PAPER
Reference: Erickson–Jones, arXiv:2412.08997v4, Definition 2.8 and Problem 5.1:
https://arxiv.org/html/2412.08997v4#S2
https://arxiv.org/html/2412.08997v4#S5

TableHolds uses normalized joint coordinates (1,x1,...,x4,y1,...,y4). Its p-long edges, reflection tie-breaks, and strict lexicographic ordering agree with the paper. The ten short-distance equalities encode its bar rules and additive table relations. Extra sortedness and upper-bound conditions are redundant: positive matched diagonal entries and additivity order y, while canonical long-count bounds imply x4<1 and y4<1. For p≠q, the long-count chambers are disjoint, so x≠y is automatic. The relevant exports use only the five allowed chamber pairs. No mathematical mismatch was found. However, equivalence to the paper's original formulation remains a mathematical audit, not a separately formalized Lean bridge theorem.

NOVELTY AND LIMITS
The paper already provides the number 22 and the finite classification. This package does not discover a new list of homometric classes. Its added structural content is a generic collision-based inclusion criterion and a compact, independently kernel-checked proof of maximality for the displayed representatives. I have not established literature-wide novelty of that general observation.

ForcedCollision still refers to equality over an entire real solution locus. Its definition alone is therefore not an intrinsic combinatorial characterization of permutations. The samples and row certificates make verification compact once candidates have been supplied; they do not select every maximal representative a priori. No theorem excludes a twenty-third maximal locus, covers every feasible table by these 22, or proves completeness of a proposed graph/circuit obstruction rule. Problem 5.1 must remain explicitly open in the description of this work.


## Publication replay limitation

The original independent source rebuild **passed all 20 project modules**, followed by the independent aggregate and theorem/axiom export checks. Before this release, all 20 recorded source hashes and successful object hashes were rechecked, and every one of the 22 published Lean source hashes matched the frozen audit manifest.

The separate new public-wrapper replay is **incomplete because of a 6 GiB resident-memory cutoff**. It completed the first 14 modules, then was stopped during `CompactGlobalB6`; the remaining seven modules and fixtures were not attempted in that run. No Lean diagnostic error was emitted before termination. The release relies on the original completed independent source rebuild, not on a claimed full pass of this resource-limited replay. The exact source closure and portable wrapper are supplied for reproduction with sufficient memory.
