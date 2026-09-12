# Direct products of finitely generated soluble Hopfian groups

A Lean 4 formalisation of the affirmative answer to Kourovka Problem 5.38:
**the direct product of two finitely generated soluble Hopfian groups is Hopfian.**

## The formalised problem

A group is **Hopfian** if each of its surjective endomorphisms is injective.
The factors may have arbitrary centres, and endomorphisms of their ordinary
external direct product may mix the factors.

The definition `ProductHopficityStatement` in
[Problem.lean](Kourovka/Problem.lean) records finite generation, solubility and
Hopficity for each factor. The result is proved as
`directProduct_isHopfian` in [CentralHopfian.lean](Kourovka/CentralHopfian.lean):

```lean
theorem directProduct_isHopfian
    [Group.FG A] [Group.FG B] [IsSolvable A] [IsSolvable B]
    (hA : IsHopfian A) (hB : IsHopfian B) : IsHopfian (A × B)
```

The declaration `problem_5_38` in [Paper.lean](Kourovka/Paper.lean) assembles
this result with the exact problem definition. All declaration names below
are in the namespace `Kourovka`.

## Central products and a bound on nonabelian images

For a finitely generated abelian group $M$, define

```math
b(M)=\mathrm{rank}_{\mathbb{Z}}(M)+|\mathrm{Tor}(M)|-1.
```

Here the two terms are the rank and the order of the torsion subgroup.
This weight is positive for nonzero $M$ and satisfies

```math
b(M\oplus N)\ge b(M)+b(N).
```

[AbelianWeight.lean](Kourovka/AbelianWeight.lean) proves these properties.
For a finitely generated group $H$, set

```math
w(H)=b\bigl((H/Z(H))_{\mathrm{ab}}\bigr).
```

[SolvableWeight.lean](Kourovka/SolvableWeight.lean) and
[CenterWeight.lean](Kourovka/CenterWeight.lean) show that $w(H)>0$ whenever
$H$ is soluble and nonabelian.

If $H=PQ$ for commuting subgroups $P,Q$, then
`CentralProducts.quotientEquiv` in
[CentralProducts.lean](Kourovka/CentralProducts.lean) constructs

```math
H/Z(H)\cong P/Z(P)\times Q/Z(Q).
```

When $P,Q$ are finitely generated, `CenterWeight.split` deduces
$w(P)+w(Q)\le w(H)$. This bounds the number of nonabelian images in each
level of the component-path construction.

## Component paths and mixed iterates

Let $f$ be a surjective endomorphism of $G=A\times B$, and let $e_0,e_1$
be the coordinate projections regarded as endomorphisms of $G$.
For a binary word $v=i_0\cdots i_{n-1}$, define

```math
p_v=e_{i_0}f\cdots e_{i_{n-1}}f,\qquad P_v=p_v(G).
```

The maps are composed from right to left. At each fixed length, their images
commute pairwise and generate $G$. Moreover, $P_v=P_{v0}P_{v1}$ with commuting
children. These identities are proved in [Paths.lean](Kourovka/Paths.lean)
and [PathExpansion.lean](Kourovka/PathExpansion.lean).

For finitely generated soluble factors, the weight bound implies that only
finitely many infinite binary paths have nonabelian images at every level.
The shift on this finite set has an idempotent positive iterate.
`ProductPaths.finitePath_middle_eq_terminal` in
[PathExtension.lean](Kourovka/PathExtension.lean) consequently gives a positive integer
$m$ such that every word $v$ of length greater than $2m$ with nonabelian
$P_v$ has $v_m=v_{2m}$, using zero-based indices.

`ProductPaths.mixed_iterate_central` in
[MixedPaths.lean](Kourovka/MixedPaths.lean) applies this constraint to obtain

```math
f^m e_j f^m e_k(G)\le Z(G)\qquad(j\ne k).
```

## Eventual centrality of the off-diagonal components

`CenterQuotients.retract_trivial_of_killed` in
[CenterQuotients.lean](Kourovka/CenterQuotients.lean) proves that a soluble
retract of a finitely generated group is trivial if a surjective endomorphism
kills it. Its proof passes to abelianisation and uses the fact that a perfect
soluble group is trivial.

[EventualCentrality.lean](Kourovka/EventualCentrality.lean) applies this
retract argument modulo the centre. The resulting declaration
`exists_central_offDiagonal_iterate` states that every surjective
endomorphism $f$ of a product of finitely generated soluble groups has
some positive power $F=f^m$ satisfying

```math
F_{12}(B)\le Z(A),\qquad F_{21}(A)\le Z(B).
```

Here $F_{12}(b)$ is the first coordinate of $F(1,b)$, and $F_{21}(a)$ is
the second coordinate of $F(a,1)$. **This result does not assume that either
factor is Hopfian.**

## Integral lifts and central corrections

[CentralLattice.lean](Kourovka/CentralLattice.lean) proves an integral
correction result. Fix a homomorphism $c:Z\to M$ of abelian groups, with
$M$ finitely generated. `CentralLattice.exists_uniform_correction_modulus`
produces an integer $d\ne0$ with the following property: if an endomorphism
$u$ preserves $c(Z)$, satisfies $u(M)+c(Z)=M$, and is the identity modulo
$dM$, then there is a homomorphism $h:M\to Z$ such that $u+c\circ h$ is
surjective. The proof uses saturation, an integral denominator and control
of torsion. No finite-generation assumption is imposed on $Z$.

`CentralLattice.exists_group_correction_modulus` transfers this construction
to a finitely generated group $G$. Assume an endomorphism $u$ preserves
$Z(G)$, satisfies $u(G)Z(G)=G$, is surjective on $G'$, and induces the
identity modulo the chosen integer on $G_{\mathrm{ab}}$. Then a
centre-valued homomorphism $h$ makes

```math
\widetilde{u}(x)=u(x)h(x)
```

surjective. The declaration `centralCorrection_eq_on_commutator` in
[Components.lean](Kourovka/Components.lean) proves that this correction agrees
with $u$ on $G'$. Then `centralCorrection_injective_on_derived` in
[DerivedReduction.lean](Kourovka/DerivedReduction.lean) deduces injectivity
of $u$ on $G'$ when $G$ is Hopfian.

## Injectivity and the product theorem

The declaration `injective_of_central_offDiagonal_hopfian` in
[CentralHopfian.lean](Kourovka/CentralHopfian.lean) proves that a surjective
endomorphism of $A\times B$ is injective if both off-diagonal images are
central and both factors are finitely generated and Hopfian.
**Solubility is not required for this injectivity criterion.**

The diagonal maps need not themselves be surjective. A common positive
iterate provides the congruences needed for central corrections, via
[CentralPeriod.lean](Kourovka/CentralPeriod.lean) and
[DiagonalCongruence.lean](Kourovka/DiagonalCongruence.lean).
Hopficity of the factors makes the corrected maps injective, hence the
diagonal maps are injective on the derived subgroups. Since the kernel of
the product endomorphism lies in $A'\times B'$, it is trivial.

Combining this criterion with eventual centrality proves
`directProduct_isHopfian`, and therefore `problem_5_38`.

## Build and verification

With Lean installed through elan, run

```sh
./scripts/check.sh
```

The package pins Lean and Mathlib to version 4.24.0 and has no dependency
on another Kourovka project. The script builds the library, runs the
transitive axiom audit in [Audit.lean](Audit.lean), and checks the exact
problem statement in [Completion.lean](Completion.lean). The only permitted
axioms are `propext`, `Classical.choice` and `Quot.sound`.
