# Roadmap: Krull-Schmidt categories and Auslander-Reiten theory of Artin algebras

**Summary.** An **Artin algebra** is an algebra `A` over a commutative Artinian ring `R` that is
finitely generated as an `R`-module. Finite-dimensional algebras over a field are the case `R = k`,
but the class is wider: `ℤ/p²ℤ`, orders reduced modulo a power of `p`, and finite rings are Artin
algebras over rings that are not fields. Auslander-Reiten theory works for this whole class, and the
reason is categorical: the module category of an Artin algebra is a Hom-finite Krull-Schmidt exact
category with an Auslander-Reiten duality, and almost-split sequences exist in every such category.
Auslander's functorial viewpoint makes the same theory visible in the category of finitely presented
functors, where almost-split sequences are minimal projective resolutions of simple functors. This
roadmap builds Krull-Schmidt categories, finitely presented functors, Matlis duality over a
commutative Artinian ring, `Ext¹` and almost-split conflations of exact categories, the
Auslander-Reiten theory of Artin algebras with its valued quiver, the classical finiteness theorems,
and global and dominant dimension. Its three summits are **existence of almost-split sequences for
Artin algebras**, as the case `mod A` of existence of almost-split conflations in a Hom-finite
Krull-Schmidt exact category with an Auslander-Reiten duality; **Auslander's theorem**: a connected
Artin algebra with a component of the Auslander-Reiten quiver of bounded length is
representation-finite, and that component is the whole quiver; and the **Auslander
correspondence**: representation-finite Artin algebras correspond, up to Morita equivalence, to
Artin algebras of global dimension at most two and dominant dimension at least two, as the case of an
additive generator in the **Morita-Tachikawa correspondence** between generator-cogenerators and
algebras of dominant dimension at least two.

## Scope and ownership

This roadmap owns:

- Krull-Schmidt categories in general: the local-endomorphism-ring characterization of
  indecomposables, idempotent completeness, uniqueness of decompositions, the recognition theorem for
  Hom-finite categories over a commutative Artinian ring with its Fitting lemma and summand
  decomposition, closure properties, additive generators, and the radical of a preadditive category
  as a morphism ideal with its powers (Layer 0);
- finitely presented functors on an additive category, the Freyd-Auslander criterion, the
  comparison with finitely presented modules, projective dimension at most two, and projective
  covers of finitely generated functors (Layer 1);
- the passage from Matlis duality over local rings to commutative Artinian rings and to Artin
  algebras, with the Nakayama functor and finitely generated injective hulls (Layer 2);
- the `Ext¹` of an exact category, its long exact sequences, the Ext-trivial morphism ideals,
  almost-split conflations with their extension-class criterion and functorial description,
  Auslander-Reiten duality, and the existence theorem for almost-split conflations (Layer 3);
- the translate, the Auslander-Reiten formulas, almost-split sequences, and source and sink maps for
  Artin algebras (Layer 4);
- irreducible-morphism bimodules, valued translation quivers and the valued Auslander-Reiten quiver
  (Layer 5);
- representation-finiteness of Artin algebras, the Harada-Sai lemma, nilpotence of the radical,
  Auslander's theorem, the first Brauer-Thrall conjecture and the infinite radical (Layer 6);
- projectivization, Morita theory for Artin algebras, the global dimension of noncommutative rings,
  dominant dimension, and the Morita-Tachikawa and Auslander correspondences (Layer 7).

The generality is fixed: the base is a commutative Artinian ring `R`, never only a field, and the
categorical results are stated for arbitrary preadditive, additive or exact categories, never only
for categories of modules. The boundaries are as follows.

- **[Quiver representations](../QuiverRepresentations/README.md), Layer 6** (sublayers 6A-6F)
  develops Auslander-Reiten theory for a finite-dimensional algebra over a field. Layers 0 and 3 to 5
  here state the same theory for Artin algebras and for exact categories, and the general
  constructions **replace** the field ones: the field declarations are the case `R = k`, with
  `E_k = k`, and where a definitional identification is unavailable they are derived from the
  general ones through a comparison isomorphism. No parallel construction is kept. The arrow counts
  of that layer's `arQuiver k A` (6F) are recovered from the valued quiver of Layer 5 here.
- **[Derived and module algebra](../../DerivedModuleAlgebra/README.md), §1.M.2** owns Matlis duality
  over a Noetherian local ring, including existence of the injective hull `E(κ)` of the residue
  field. Layer 2 here consumes it for the local factors of a commutative Artinian ring and owns only
  the passage to Artinian rings that are not local and to Artin algebras.
- **[Grothendieck groups and Euler forms](../../GrothendieckEulerForms/README.md)** owns exact
  structures and conflation-exact functors. **[Stable, periodic and curved
  categories](../../StablePeriodicCurved/README.md), Layer 0**, owns relative projectives and
  injectives, enough of them, Frobenius exact categories and the stable category as the quotient by
  the factoring ideal. This roadmap consumes both and owns `Ext¹`, almost-split conflations,
  Auslander-Reiten duality, and the Ext-trivial ideals `𝒫_E` and `ℐ_E` that duality needs for exact
  categories without enough projectives or injectives, compared there with the factoring ideals.
- **[Purity of the branch locus](../../PurityOfBranchLocus/README.md), §0.3** owns the global
  dimension of a commutative ring (`TauCetiRoadmap.PurityOfBranchLocus.globalDimension`) with its
  finite-module and cyclic-module criteria and localization bounds. Layer 7 here owns its extension
  to noncommutative rings, left and right, and the Artin-algebra results; on a commutative ring the
  two definitions are the same supremum, and the commutative results are imported from §0.3, not
  proved again.
- **[Enhanced derived sheaves](../../EnhancedDerivedSheaves/README.md)** bounds projective
  dimensions over regular commutative rings. It is not consumed here.
- **[Geometric representation categories](../../GeometricRepresentationCategories/README.md),
  §R5.2** owns the generic comparison, in an abelian category with `HasExt`, between the Baer sum of
  extensions and addition of Mathlib's extension classes. Layer 3 here reuses it and owns only the
  exact-category `Ext¹` and its comparison with that construction.
- Outside this roadmap: Auslander-Reiten triangles, Serre functors, derived categories and
  extriangulated categories; tilting and τ-tilting theory; covering theory; modules that are not
  finitely generated, except in the definitions of global dimension and of Morita equivalence; a
  theory of functors that are not finitely presented (the category of all additive functors appears
  only as the ambient category of `mod C`, of the simple functors `S_Z` and of the radical functors
  `rad(-, Z)`), Grothendieck categories, purity, the defect formula and Auslander's formula,
  Krull-Gabriel dimension, and the description of whole components of the Auslander-Reiten quiver
  through functors; coherent rings as a ring-theoretic notion (they enter only through the
  Freyd-Auslander criterion of Layer 1); and dominant dimension of rings other than Artin algebras,
  where the terms of the minimal injective coresolution are asked to be flat rather than projective
  (Hoshino). For Artin algebras the two conditions agree; for other rings the flat version needs
  flatness over noncommutative rings, which Mathlib does not have (`Module.Flat` is stated over
  commutative rings).

Suggested homes in Tau Ceti are `TauCeti/CategoryTheory/KrullSchmidt/`,
`TauCeti/CategoryTheory/FinitelyPresentedFunctor/`, `TauCeti/CategoryTheory/Exact/` (for `Ext¹` and
almost-split conflations), `TauCeti/RingTheory/Matlis/`, and
`TauCeti/RepresentationTheory/ArtinAlgebra/`.

## Conventions

1. `R` is a commutative Artinian ring. An **Artin `R`-algebra** is `[Ring A] [Algebra R A]
   [Module.Finite R A]`. Modules are left modules, and `mod A` is `FGModuleCat A`. No statement
   assumes `[IsAlgClosed k]`.
2. A category `C` is **Hom-finite over `R`** when it is `R`-linear (`Linear R C`) and every
   `X ⟶ Y` is a finitely generated `R`-module. Where only endomorphisms are used, the hypothesis is
   stated for `X ⟶ X` alone.
3. A **Krull-Schmidt category** is a preadditive category with finite biproducts in which every
   object is isomorphic to a finite biproduct of objects with local endomorphism rings. The zero
   object is the empty biproduct. An **additive generator** is an object of which every
   indecomposable object is a direct summand. "Direct summand" is Mathlib's `Retract`.
4. For an additive category `C`, a **finitely presented functor** is an additive functor
   `F : Cᵒᵖ ⥤ AddCommGrpCat` with an exact sequence `(-, X) → (-, Y) → F → 0` of representable
   functors (`preadditiveYoneda`); `mod C` is the full subcategory they form. For `X` with local
   endomorphism ring, `S_X = (-, X) / rad(-, X)` is the **simple functor** at `X`.
5. An **exact category** is a Tau Ceti `ExactStructure E` on an additive category; conflations,
   inflations and deflations are Tau Ceti's. Relative projectives and injectives and the stable
   categories are those of StablePeriodicCurved Layer 0.
6. `J(R)` is the Jacobson radical of `R`, `E_R` is an injective hull of `R ⧸ J(R)`, and
   `D_R = Hom_R(-, E_R)` is the **Matlis dual**. For a field, `E_k = k` and `D_k = Hom_k(-, k)`.
7. `Ext¹_E(Z, X)` is the group of classes of conflations `X ↪ Y ↠ Z` under the Baer sum. For the
   abelian exact structure on an abelian category it is Mathlib's `CategoryTheory.Abelian.Ext Z X 1`.
8. For `Γ = Module.End A M`, multiplication is composition, so `Hom_A(X, M)` is a left `Γ`-module by
   composition after, and `Hom_A(M, X)` is a right `Γ`-module by composition before.
9. **Morita equivalence** of Artin algebras means an `R`-linear equivalence `mod A ≌ mod B`; Layer 7
   identifies it with Mathlib's `IsMoritaEquivalent R A B`. Statements about isomorphism classes of
   indecomposable objects use Mathlib's `Skeleton`.
10. The radical `rad` of a preadditive category is Tau Ceti's `TauCeti.jacobsonRadical`: `f : X ⟶ Y`
    lies in `rad(X, Y)` when `𝟙 - g ≫ f` is invertible for every `g : Y ⟶ X`. Its powers are
    those of the morphism ideal of Layer 0.

**Sources and locators.** [ARS] is Auslander-Reiten-Smalø, [ASS] is Assem-Simson-Skowroński
Volume 1, [Kr] is Krause's Krull-Schmidt paper, [En] is Enomoto's exact-structures paper, [INP] is
Iyama-Nakaoka-Palu, and the other works are cited by author; see the References. Every numbered locator
has been checked against the source: [ARS] and [ASS] in their printed numbering, Harada-Sai in the
journal numbering, and the arXiv papers in the versions 1410.2822v1, 1705.02163v4 and 1805.03776v3. A
section given without a number means that the statement is in the running text of that section.

## Exact supplier contracts

The baseline is Mathlib `f6090c7095e1e56b3464c1daba5f24631f1290d2` and Tau Ceti
`358314d4ab97483df4fc4cb8adcc02e74a8d9f5a`.

### From Mathlib

- Categories: `CategoryTheory.Preadditive`, `CategoryTheory.Linear`,
  `CategoryTheory.Limits.HasFiniteBiproducts`, `CategoryTheory.Indecomposable`,
  `CategoryTheory.IsIdempotentComplete`, `CategoryTheory.Idempotents.Karoubi`,
  `CategoryTheory.Retract`, `CategoryTheory.Skeleton`, `CategoryTheory.ObjectProperty.FullSubcategory`,
  `CategoryTheory.Limits.HasWeakKernels`, `CategoryTheory.preadditiveYoneda`, `AddCommGrpCat`.
- Homological algebra: `CategoryTheory.ShortComplex` with `ShortComplex.Exact` and
  `ShortComplex.ShortExact`, `CategoryTheory.Abelian.Ext` with `ShortComplex.ShortExact.extClass`,
  `CategoryTheory.Projective`, `CategoryTheory.Injective`, `CategoryTheory.EnoughProjectives`,
  `CategoryTheory.EnoughInjectives`, `CategoryTheory.projectiveDimension`,
  `CategoryTheory.HasProjectiveDimensionLE`, `CategoryTheory.HasProjectiveDimensionLT`.
- Modules and rings: `ModuleCat`, `FGModuleCat`, `Module.Finite`, `Module.End`, `IsLocalRing`,
  `Ring.jacobson`, `IsArtinianRing` with `IsArtinianRing.quotNilradicalPowEquivPi`,
  `IsNoetherianRing`, `IsSemiprimaryRing`, `IsFiniteLength`, `Module.length`, `MulOpposite`,
  `LinearMap.applyₗ`, the scoped `ModuleCat.Algebra` instances.
- Morita theory: `MoritaEquivalence`, `IsMoritaEquivalent` and `IsMoritaEquivalent.matrix`.
- Quivers: `Quiver`, `Quiver.WeaklyConnectedComponent`.

### From Tau Ceti

- Almost-split maps and sequences in an arbitrary category: `TauCeti.IsLeftAlmostSplit`,
  `TauCeti.IsRightAlmostSplit` (`TauCeti.CategoryTheory.AlmostSplit.Basic`) and
  `ShortComplex.IsAlmostSplit` (`TauCeti.CategoryTheory.AlmostSplit.Sequence`).
- Irreducible morphisms: `TauCeti.IsIrreducibleMorphism` (`TauCeti.CategoryTheory.IrreducibleMorphism`).
- The radical: `TauCeti.jacobsonRadical` and `TauCeti.jacobsonRadicalSq` (additive subgroups of
  each Hom group), `TauCeti.mem_jacobsonRadical_iff_not_isIso` for objects with local endomorphism
  rings, `TauCeti.jacobsonRadical_self_eq_jacobson`, and
  `TauCeti.isIrreducibleMorphism_iff_mem_jacobsonRadical_and_notMem_jacobsonRadicalSq`
  (`TauCeti.CategoryTheory.Preadditive.Radical.Basic`).
- Morphism ideals and their quotients: `TauCeti.MorphismIdeal`, `TauCeti.MorphismIdeal.Quotient`
  (`TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic`).
- Krull-Schmidt for modules of finite length: `TauCeti.exists_indecomposable_iso_biproduct` and
  `TauCeti.exists_equiv_iso_of_iso_biproduct` (`TauCeti.Algebra.Category.ModuleCat.KrullSchmidt`);
  for pointwise finite-dimensional quiver representations,
  `TauCeti.QuiverRep.exists_equiv_iso_of_iso_biproduct`
  (`TauCeti.RepresentationTheory.Quiver.Representation.KrullSchmidt`).
- Exact structures: `TauCeti.ExactStructure` (`TauCeti.CategoryTheory.Exact.Abelian` and the modules
  it imports), with the projective stable category `TauCeti.ExactStructure.ProjectiveStableCategory`
  (`TauCeti.CategoryTheory.Exact.Stable.Basic`).
- Injective hulls: `TauCeti.IsInjectiveEnvelope` and `TauCeti.IsInjectiveEnvelope.exists_linearEquiv`
  (`TauCeti.Algebra.Module.Injective.Envelope.Basic`).
- Projective covers over Artinian rings: `TauCeti.exists_projectiveCover`
  (`TauCeti.Algebra.Module.ProjectiveCover.ModuleCat`).
- The transpose over an arbitrary ring and its stable equivalence: `TauCeti.AuslanderReitenTranspose`
  (`TauCeti.Algebra.Module.AuslanderReiten.Transpose`) and `TauCeti.stableTransposeEquivalence`
  (`TauCeti.Algebra.Module.AuslanderReiten.Equivalence`).
- The translate of a presentation over a field, `TauCeti.AuslanderReitenTranslate`
  (`TauCeti.Algebra.Module.AuslanderReiten.Translate`), and of a quiver representation,
  `TauCeti.arTranslate` (`TauCeti.RepresentationTheory.Quiver.Representation.Translate`).
- Morita theory: `IsIdempotentElem.isMoritaEquivalent_corner` (`TauCeti.RingTheory.Morita.Corner`),
  `CategoryTheory.Equivalence.finiteModulesEquivalence` and
  `CategoryTheory.Equivalence.finiteProjectiveModulesEquivalence`
  (`TauCeti.Algebra.Category.ModuleCat.CartanMap.Morita`).

### From other roadmaps

- DerivedModuleAlgebra §1.M.2: for a Noetherian local ring, an injective hull `E(κ)` of the residue
  field, and Matlis duality between Artinian modules and finite modules over the completion. Layer 2
  uses it for local Artinian rings, which are complete.
- GrothendieckEulerForms: exact structures, conflation-exact functors and the abelian exact
  structure.
- StablePeriodicCurved Layer 0: relative projective and injective objects, enough relative
  projectives and injectives, and the stable categories `E/[P]` and `E/[I]` as quotients by the
  factoring ideals.
- PurityOfBranchLocus §0.3: `globalDimension` of a commutative ring with `globalDimension_le_iff`,
  `globalDimension_le_iff_hasProjectiveDimensionLE` and the localization bounds.
- GeometricRepresentationCategories §R5.2: the comparison of the Baer sum with addition of
  `extClass` in an abelian category with `HasExt`.
- QuiverRepresentations Layer 6 (6A-6F): the field case, which Layers 0 and 3 to 5 here replace.

## How to read the build

| Layer | Construction | Principal outputs |
| --- | --- | --- |
| [0](#layer-0-krull-schmidt-categories) | Krull-Schmidt categories | Local endomorphism rings, uniqueness, recognition over Artinian rings, additive generators, the radical ideal |
| [1](#layer-1-finitely-presented-functors) | Finitely presented functors | `mod C`, the Freyd-Auslander criterion, `mod (proj A)`, projective dimension two, projective covers |
| [2](#layer-2-matlis-duality-over-a-commutative-artinian-ring) | Matlis duality | `E_R`, `D_R`, the duality for Artin algebras, the Nakayama functor, injective hulls |
| [3](#layer-3-ext-and-almost-split-conflations-in-exact-categories) | Exact categories | `Ext¹`, Ext-trivial ideals, almost-split conflations, Auslander-Reiten duality, existence |
| [4](#layer-4-auslander-reiten-theory-of-artin-algebras) | Artin algebras | `τ`, the Auslander-Reiten formulas, almost-split sequences, source and sink maps |
| [5](#layer-5-the-valued-auslander-reiten-quiver) | The valued quiver | Irreducible-morphism bimodules, valuations, the mesh, multiplicities |
| [6](#layer-6-finiteness-theorems) | Finiteness | Harada-Sai, nilpotence of the radical, Auslander's theorem, Brauer-Thrall I, `rad^∞` |
| [7](#layer-7-morita-theory-global-and-dominant-dimension-and-the-correspondences) | Dimensions and correspondences | Projectivization, Morita theory, `gl.dim`, `dom.dim`, Morita-Tachikawa, Auslander |

Layers 0, 1 and 2 are independent, except that the projective covers of Layer 1 use Layer 0. Layer 3
needs Layer 0 for Krull-Schmidt, Layer 1 for the functorial picture and Layer 2 for `D_R`. Layer 4
needs Layers 2 and 3. Layer 5 needs Layers 0 and 4. Layer 6 needs Layers 4 and 5; its Harada-Sai
lemma needs only Layer 0. Layer 7 needs Layer 0 for additive generators, Layer 1 for
projectivization and the bound on projective dimension, and Layer 2 for injective hulls and
projective-injectives.

The names below are the intended Lean names. Those also stated in `Suggested.lean` are marked
"(in `Suggested.lean`)"; the others are specified here only.

## Layer 0: Krull-Schmidt categories

### 0.1 Local endomorphism rings and indecomposables

**Local endomorphism rings give indecomposables** (`indecomposable_of_isLocalRing_end`). In a
preadditive category with binary biproducts, an object whose endomorphism ring is local is
indecomposable: an idempotent of a local ring is `0` or `1`.

**Checks.**

- The zero object is not indecomposable, and its endomorphism ring, the zero ring, is not local.
- `ℤ` is an indecomposable `ℤ`-module whose endomorphism ring `ℤ` is not local, so the converse
  fails outside Krull-Schmidt categories.
- For a field `k`, the module `k` has endomorphism ring `k`, which is local.

*Needs:* Mathlib `CategoryTheory.Indecomposable`, `IsLocalRing`,
`CategoryTheory.Limits.HasBinaryBiproducts`.

**Fitting's lemma** (`isLocalRing_end_of_indecomposable`). In an idempotent-complete preadditive
category with binary biproducts that is Hom-finite over a commutative Artinian ring `R` (Convention
2, for endomorphisms), an indecomposable object has local endomorphism ring. The endomorphism ring
is an Artin `R`-algebra, every element is a unit or nilpotent on the image of a high enough power
(Fitting), and a nontrivial idempotent splits off a summand.

**Checks.**

- For `R = ℤ/4ℤ`, the modules `ℤ/2ℤ` and `ℤ/4ℤ` are indecomposable with local endomorphism rings
  `ℤ/2ℤ` and `ℤ/4ℤ`.
- `ℤ`, an indecomposable `ℤ`-module, has `End ℤ = ℤ` of infinite length over `ℤ`, and `ℤ` is not
  Artinian; the conclusion fails there.
- Without idempotent completeness the conclusion fails: in the full subcategory of free modules over
  `k × k`, the object `k × k` has no proper nonzero summand in the subcategory, so it is
  indecomposable there, but its endomorphism ring `k × k` is not local.

*Needs:* Mathlib `IsArtinianRing`, `Module.Finite`, `CategoryTheory.IsIdempotentComplete`; 0.1's
`indecomposable_of_isLocalRing_end`.

### 0.2 Krull-Schmidt categories

**The class** (`IsKrullSchmidt`, in `Suggested.lean`). A preadditive category with finite
biproducts is Krull-Schmidt when every object is isomorphic to a finite biproduct of objects with
local endomorphism rings.

Provide transport along equivalences of categories (`IsKrullSchmidt.of_equivalence`),
`indecomposable_iff_isLocalRing_end` (in `Suggested.lean`), and
`isIdempotentComplete_of_isKrullSchmidt` (in `Suggested.lean`): a Krull-Schmidt category is
idempotent complete ([Kr, proof of Cor. 4.4], from Prop. 2.3 and Cor. 4.3).

**Checks.**

- The zero object is the empty biproduct (`n = 0`), so the category with one object and one
  morphism is Krull-Schmidt.
- `mod (ℤ/4ℤ)` is Krull-Schmidt, with indecomposables `ℤ/2ℤ` (length 1) and `ℤ/4ℤ` (length 2).
- Finitely generated abelian groups do not form a Krull-Schmidt category: `ℤ` is indecomposable and
  `End ℤ = ℤ` is not local.

*Needs:* 0.1's `indecomposable_of_isLocalRing_end`; Mathlib `CategoryTheory.IsIdempotentComplete`,
`CategoryTheory.Equivalence`.

### 0.3 Uniqueness of decompositions

**Uniqueness** (`exists_equiv_iso_of_iso_biproduct`, in `Suggested.lean`). If `⨁ i, X i ≅ ⨁ j, Y j`
with all `End (X i)` and `End (Y j)` local, there is a bijection `σ` of the index types with
`X i ≅ Y (σ i)`. The proof is the exchange argument in the category ([Kr, Thm. 4.2 and Cor. 4.3]),
generalizing the module statement `TauCeti.exists_equiv_iso_of_iso_biproduct`, which becomes its
case `ModuleCat`.

**Checks.**

- With empty index types, the statement is the uniqueness of the empty decomposition of `0`.
- In `mod (ℤ/4ℤ)`, `ℤ/2ℤ ⊞ ℤ/4ℤ` and `ℤ/4ℤ ⊞ ℤ/4ℤ` are not isomorphic, since their summands do not
  match.
- Without local endomorphism rings uniqueness fails: over `ℤ[√-5]`, the ideal
  `I = (2, 1 + √-5)` is an indecomposable non-free projective module with `I ⊕ I ≅ R ⊕ R`, since
  `I²` is principal (Steinitz).

*Needs:* 0.2's `IsKrullSchmidt`; Tau Ceti `TauCeti.exists_equiv_iso_of_iso_biproduct` as the module
case to be derived.

### 0.4 Recognition over a commutative Artinian ring

**Summand decomposition** (`exists_isLocalRing_end_sum_comp_eq_id`). In a preadditive category
that is Hom-finite over a commutative Artinian ring `R` (for endomorphisms), every object `X` has
finitely many idempotent endomorphisms `e i`, pairwise orthogonal, with `∑ i, e i = 𝟙 X`, whose
corners `e i ≫ End X ≫ e i` are local rings. The proof decomposes `1` in the Artin `R`-algebra
`End X` into primitive orthogonal idempotents; no idempotent completeness is needed.

**Checks.**

- For `X = 0` the family is empty.
- In `mod (ℤ/4ℤ)`, `X = ℤ/2ℤ ⊞ ℤ/4ℤ` gets two idempotents, the projections onto the two summands.
- In an abstractly presented category, the one-object category with endomorphism ring `k × k`, the
  identity is `(1, 0) + (0, 1)` with local corners `k`, although the object has no splitting there.

*Needs:* Mathlib `IsArtinianRing`, `Module.Finite`, `IsLocalRing`; Tau Ceti
`TauCeti.jacobsonRadical_self_eq_jacobson`.

**Recognition** (`isKrullSchmidt_of_module_finite`, in `Suggested.lean`). An idempotent-complete
category with finite biproducts that is Hom-finite over a commutative Artinian ring is
Krull-Schmidt. The category is arbitrary, not a category of modules: idempotent completeness turns
the summand decomposition into a biproduct decomposition. Equivalently, by [Kr, Cor. 4.4] (split
idempotents and semiperfect endomorphism rings), since the endomorphism ring of each object is an
Artin `R`-algebra and hence semiperfect; for a complete local Noetherian base this is [En, §3.2].

**Checks.**

- `mod (ℤ/4ℤ)` is recognized, with indecomposables of lengths 1 and 2.
- The Karoubi envelope (`CategoryTheory.Idempotents.Karoubi`) of the one-object category with
  endomorphism ring `k × k`, an abstract idempotent-complete category that is not presented as a
  category of modules, is recognized; its indecomposables are the two images of `(1, 0)` and
  `(0, 1)`.
- The full subcategory of free modules over `k × k` is Hom-finite over `k` but not idempotent
  complete, and is not Krull-Schmidt (0.1).

*Needs:* 0.4's `exists_isLocalRing_end_sum_comp_eq_id`; 0.1's `isLocalRing_end_of_indecomposable`;
0.2's `IsKrullSchmidt`; Mathlib `CategoryTheory.IsIdempotentComplete`.

### 0.5 Closure, instances and additive generators

**Closure** (`IsKrullSchmidt.of_fullSubcategory`). A full subcategory of a Krull-Schmidt category
that is closed under isomorphisms, finite biproducts and direct summands is Krull-Schmidt.

**Instances.** `mod A` for an Artin algebra `A` (`FGModuleCat.isKrullSchmidt`), finite-length
modules over an arbitrary ring, and pointwise finite-dimensional representations of a finite quiver
are Krull-Schmidt; the module and quiver cases recover `TauCeti.exists_indecomposable_iso_biproduct`
and `TauCeti.QuiverRep.exists_equiv_iso_of_iso_biproduct`.

**Additive generators** (`IsAdditiveGenerator`, in `Suggested.lean` for `mod A`;
`exists_isAdditiveGenerator_iff_finite`). A Krull-Schmidt category has an additive generator exactly
when it has finitely many isomorphism classes of indecomposable objects; the sum of one
indecomposable from each class is one.

**Checks.**

- `ℤ/2ℤ ⊞ ℤ/4ℤ` is an additive generator of `mod (ℤ/4ℤ)`.
- For a semisimple Artin algebra, the sum of the simple modules, one of each class, is an additive
  generator.
- `mod` of the Kronecker algebra over a field has infinitely many indecomposables up to isomorphism
  and no additive generator.

*Needs:* 0.2's `IsKrullSchmidt`, 0.4's `isKrullSchmidt_of_module_finite`; Mathlib `Skeleton`,
`CategoryTheory.Retract`; Tau Ceti `TauCeti.exists_indecomposable_iso_biproduct`.

### 0.6 The radical as a morphism ideal

**The radical ideal** (`jacobsonRadicalIdeal`, with powers `jacobsonRadicalIdeal C ^ n`). The
subgroups `TauCeti.jacobsonRadical X Y` form a morphism ideal (`TauCeti.MorphismIdeal`). Its powers
are the ideals generated by `n`-fold composites. Provide the biproduct description: for
decompositions `X ≅ ⨁ i, X i` and `Y ≅ ⨁ j, Y j` into objects with local endomorphism rings,
`f ∈ rad(X, Y)` exactly when no component `X i ⟶ Y j` of `f` is an isomorphism (from
`TauCeti.mem_jacobsonRadical_iff_not_isIso`). Prove that `rad²` agrees with Tau Ceti's
`TauCeti.jacobsonRadicalSq`, so that irreducible morphisms are the maps in `rad \ rad²`.

**Checks.**

- In `mod k`, the radical is zero.
- For `B = k[ε]/(ε²)`, the radical of the category `mod B` has `rad² ≠ 0` and `rad³ = 0`: the
  composite `B → k → B` is multiplication by `ε`, a nonzero element of `rad²(B, B)`, while every
  composite of three non-isomorphisms between `k` and `B` vanishes.
- By contrast the ring radical of `End_B(B) ≅ B` is `(ε)`, whose square is zero: the categorical
  `rad²(B, B)` is not the square of the ring radical of `End_B(B)`.

*Needs:* Tau Ceti `TauCeti.jacobsonRadical`, `TauCeti.jacobsonRadicalSq`,
`TauCeti.mem_jacobsonRadical_iff_not_isIso`, `TauCeti.MorphismIdeal`; 0.3's uniqueness.

### Examples

`mod (ℤ/4ℤ)` and `mod (k[ε]/(ε²))` run through the whole layer: two indecomposables each, an
additive generator, and a radical with `rad³ = 0`. The one-object category on `k × k` and its Karoubi
envelope separate the summand decomposition from the Krull-Schmidt property.

### Dependencies

Mathlib category theory and Artinian rings; Tau Ceti's radical, morphism ideals and module
Krull-Schmidt theorem.

## Layer 1: finitely presented functors

### 1.1 The category `mod C`

**Finitely presented functors** (`IsFinitelyPresentedFunctor`, in `Suggested.lean`). For an
additive category `C`, the finitely presented functors (Convention 4) form a full subcategory
`mod C` of the additive functors `Cᵒᵖ ⥤ AddCommGrpCat`, closed under cokernels and extensions; the
representable functors `(-, X)` are projective in it, and every object has a presentation by
representables (Yoneda). A **finitely generated** functor is a quotient of a representable functor.

**Checks.**

- Every representable functor `(-, X)` is finitely presented, with `X = 0` in the presentation.
- The zero functor is finitely presented.
- For `C = mod k`, the restriction of `(-, K)` to finite-dimensional spaces, for an
  infinite-dimensional `k`-space `K`, is not finitely generated: every map from a representable
  functor lands in `(-, K')` for a finite-dimensional `K' ⊆ K`.

*Needs:* Mathlib `CategoryTheory.preadditiveYoneda`, `ShortComplex.Exact`, `AddCommGrpCat`.

### 1.2 The Freyd-Auslander criterion

**Criterion** (`hasWeakKernels_iff_isFinitelyPresentedFunctor_kernel`, in `Suggested.lean`).
`mod C` is abelian, with kernels computed in the functor category, exactly when `C` has weak
kernels (`HasWeakKernels C`) (Auslander, *Coherent functors*, §2; Freyd).
Abelian categories have weak kernels, and so do pretriangulated ones (Mathlib).

**Checks.**

- For `C = mod A` with `A` an Artin algebra, `C` is abelian, so `mod C` is abelian.
- For the category of finitely generated free modules over a Noetherian ring, weak kernels exist,
  given by a finite free module mapping onto the kernel.
- For `A = k[x, y₁, y₂, …]/(x yᵢ)ᵢ`, the annihilator of `x` is not finitely generated, so
  multiplication by `x` on `A` has no weak kernel among finitely generated projective modules, and
  `mod (proj A)` is not abelian.

*Needs:* 1.1's `IsFinitelyPresentedFunctor`; Mathlib `CategoryTheory.Limits.HasWeakKernels`.

### 1.3 Finitely presented modules and abelian categories with enough projectives

**Rings** (`modProjEquivFinitelyPresented`). For a ring `A` and the category `proj A` of finitely
generated projective `A`-modules, evaluation at `A` identifies `mod (proj A)` with the finitely
presented `A`-modules. So the finitely presented `A`-modules form an abelian category exactly when
`proj A` has weak kernels, which the classical literature calls left coherence of `A` (Chase).

**Abelian categories with enough projectives** (`equivModProjectives`). For an abelian category `C`
with enough projectives, restriction to the projectives is an equivalence `C ≌ mod (proj C)`. When
`C` has a **progenerator** `P` (a projective object of which every object is a quotient of a finite
sum of copies), `proj C = add P`, and `Hom(P, -)` is an equivalence from `C` to the finitely
presented right `End P`-modules.

**Checks.**

- For `C = mod A` and `P = A`, `End_A(A) ≅ Aᵐᵒᵖ`, and right `Aᵐᵒᵖ`-modules are left `A`-modules.
- For `P = A ⊕ A`, `End P` is `Mat₂(A)ᵐᵒᵖ`, and the equivalence is the matrix Morita equivalence.
- For `A = k`, every finitely presented functor on `proj k` is representable.

*Needs:* 1.2's criterion; Mathlib `CategoryTheory.Projective`, `CategoryTheory.EnoughProjectives`,
`Module.End`.

### 1.4 Projective dimension at most two

**Kernels** (`hasProjectiveDimensionLE_two_iff_hasKernels`). For an idempotent-complete additive
category `C` with weak kernels, every object of `mod C` has projective dimension at most two exactly
when `C` has kernels. If `g : Y → Z` has a kernel `X`, the presentation `(-, Y) → (-, Z) → F → 0`
extends to `0 → (-, X) → (-, Y) → (-, Z) → F → 0`; conversely the kernel of `(-, Y) → (-, Z)` is
then projective, hence representable because idempotents split, and represents a kernel of `g`.

**Checks.**

- For an abelian `C`, every finitely presented functor has projective dimension at most two.
- For `C = proj ℤ`, kernels exist (subgroups of finitely generated free groups are free), so the
  bound holds.
- For `C = proj B` with `B = k[ε]/(ε²)`, weak kernels exist but multiplication by `ε` on `B` has no
  kernel in `proj B` (its kernel `εB ≅ k` is not projective), and the cokernel of
  `(-, ε) : (-, B) → (-, B)` has infinite projective dimension.

*Needs:* 1.2's criterion; Mathlib `CategoryTheory.HasProjectiveDimensionLE`,
`CategoryTheory.IsIdempotentComplete`.

### 1.5 Projective covers

**Projective covers of functors** (`IsProjectiveCover`, `exists_isProjectiveCover`). A projective
cover of a finitely generated functor `F` is an epimorphism `p : (-, P) → F` that is right minimal:
every endomorphism `φ` of `P` with `(-, φ) ≫ p = p` is an isomorphism. It is stated in the category
of additive functors, so it needs no abelian structure on `mod C` and applies to finitely generated
functors that are not finitely presented. If `C` is Krull-Schmidt, every finitely generated functor
has a projective cover, since the endomorphism rings are semiperfect ([Kr, §3 and Prop. 4.1]); for
`X` with local endomorphism ring,
`(-, X) → S_X` is a projective cover.

**Checks.**

- The zero functor has the projective cover `(-, 0) → 0`.
- For `X` with local endomorphism ring, `(-, X) → S_X` is a projective cover.
- For `C = proj ℤ`, which is not Krull-Schmidt, the cokernel of `(-, 2) : (-, ℤ) → (-, ℤ)` has no
  projective cover, as `ℤ/2ℤ` has none over `ℤ`.

*Needs:* 0.2's `IsKrullSchmidt`; 1.1's finitely generated functors; Tau Ceti
`TauCeti.jacobsonRadical`.

### Examples

For `C = mod (ℤ/4ℤ)`, `mod C` is abelian of global dimension at most two, and its simple functors
`S_{ℤ/2ℤ}` and `S_{ℤ/4ℤ}` have projective covers `(-, ℤ/2ℤ)` and `(-, ℤ/4ℤ)`.

### Dependencies

Layer 0 (projective covers); Mathlib's preadditive Yoneda embedding and weak kernels.

## Layer 2: Matlis duality over a commutative Artinian ring

### 2.1 The injective cogenerator

**Local factors.** A commutative Artinian ring is the finite product of the local Artinian rings
`R ⧸ 𝔪 ^ n` over its maximal ideals `𝔪`, for `n` with `nilradical R ^ n = ⊥`
(`IsArtinianRing.quotNilradicalPowEquivPi`). Modules over `R` split accordingly.

**`E_R`** (`exists_isInjectiveEnvelope_quotient_jacobson`, in `Suggested.lean`). An injective hull
of `R ⧸ J(R)`, assembled from the hulls `E(R ⧸ 𝔪)` of the local factors supplied by
DerivedModuleAlgebra §1.M.2, with uniqueness from `TauCeti.IsInjectiveEnvelope.exists_linearEquiv`.
`E_R` has finite length, and every simple `R`-module embeds in it.

**Checks.**

- For a field, `E_k = k`.
- For `R = ℤ/p²ℤ`, `E_R = R`, since `R` is self-injective.
- For `R = k[x, y]/(x, y)²`, `E_R` has length 3 and is not isomorphic to `R`, whose socle has
  dimension 2.

*Needs:* DerivedModuleAlgebra §1.M.2; Mathlib `IsArtinianRing.quotNilradicalPowEquivPi`,
`IsFiniteLength`; Tau Ceti `TauCeti.IsInjectiveEnvelope`.

### 2.2 The duality

**Matlis duality** (`bijective_applyₗ_of_isInjectiveEnvelope`, in `Suggested.lean`;
`matlisDualEquiv`). `D_R M = M →ₗ[R] E_R` is an exact contravariant `R`-linear functor that preserves
finite length and composition length, and the evaluation `M → D_R (D_R M)` is an isomorphism for
every `R`-module of finite length ([ARS, Thm. II.3.1]; for Artin algebras, Thm. II.3.3). So `D_R` is an
anti-equivalence of the finite-length `R`-modules with themselves.

**Checks.**

- Over `R = ℤ/p²ℤ`, `D_R (ℤ/pℤ) ≅ ℤ/pℤ` and `D_R R ≅ R`.
- `D_R` preserves length: `length (D_R M) = length M`.
- Over a field, an infinite-dimensional space is not reflexive, so the finite-length hypothesis is
  needed.

*Needs:* 2.1's `E_R`; Mathlib `LinearMap.applyₗ`, `Module.length`.

### 2.3 Artin algebras

**Duality for Artin algebras** (`matlisDualFG`). For an Artin `R`-algebra `A`, `D_R` exchanges
finitely generated left `A`-modules and finitely generated right `A`-modules, an anti-equivalence
between `mod A` and `mod Aᵐᵒᵖ`; it exchanges projectives and injectives, and `D_R A` is an injective
cogenerator of `mod A`.

**The Nakayama functor** (`nakayamaFunctor`). `ν = D_R ∘ Hom_A(-, A)` is an equivalence from
finitely generated projective to finitely generated injective `A`-modules, sending the projective
cover of a simple module to its injective hull.

**Injective hulls** (`exists_isInjectiveEnvelope_fg`). Every finitely generated `A`-module `M` has a
finitely generated injective hull, `D_R` of a projective cover of the right module `D_R M`
(`TauCeti.exists_projectiveCover`, `TauCeti.IsInjectiveEnvelope`), and hence a minimal injective
coresolution by finitely generated injective modules.

**Checks.**

- For `A = ℤ/p²ℤ`, `ν A ≅ A`, and `A` is injective in `mod A`.
- For `A = k[ε]/(ε²)`, `A` is self-injective, `ν A ≅ A`, and the injective hull of `k` is `A`.
- For the upper triangular algebra `T₂(k)`, `ν` sends the simple projective module to the
  projective-injective module of length 2, and the injective hull of the simple projective module
  is that module.

*Needs:* 2.2's duality; Tau Ceti `TauCeti.exists_projectiveCover`, `TauCeti.IsInjectiveEnvelope`;
Mathlib `MulOpposite`.

### Examples

`ℤ/p²ℤ` and `k[ε]/(ε²)` are self-injective, with `E_R = R` in the first case; `k[x, y]/(x, y)²`
shows that `E_R` need not be `R`.

### Dependencies

DerivedModuleAlgebra §1.M.2 for the local case; Tau Ceti injective hulls and projective covers.

## Layer 3: `Ext¹` and almost-split conflations in exact categories

### 3.1 `Ext¹` of an exact category

**`Ext¹`** (intended `ExactStructure.Ext1 E Z X`). Classes of conflations `X ↪ Y ↠ Z` up to
isomorphism of conflations fixing `X` and `Z`, an abelian group under the Baer sum, contravariant in
`Z` and covariant in `X` by pullback and pushout, and an `R`-module when the category is `R`-linear
(Yoneda). The zero class is the class of the split conflation. For the abelian exact structure on an
abelian category it agrees with Mathlib's `CategoryTheory.Abelian.Ext Z X 1`, through the comparison
of GeometricRepresentationCategories §R5.2.

**The long exact sequences.** For a conflation `X ↪ Y ↠ Z` and an object `W`, the sequences
`0 → Hom(W, X) → Hom(W, Y) → Hom(W, Z) → Ext¹(W, X) → Ext¹(W, Y) → Ext¹(W, Z)` and
`0 → Hom(Z, W) → Hom(Y, W) → Hom(X, W) → Ext¹(Z, W) → Ext¹(Y, W) → Ext¹(X, W)` are exact.

**Checks.**

- For the split exact structure, `Ext¹ = 0`.
- For the abelian structure on finite abelian groups, `Ext¹(ℤ/2ℤ, ℤ/2ℤ)` has two elements: the split
  class and the class of `0 → ℤ/2ℤ → ℤ/4ℤ → ℤ/2ℤ → 0`.
- Over `ℤ/4ℤ`, the same sequence gives a nonzero class in `Ext¹(ℤ/2ℤ, ℤ/2ℤ)`, which is again `ℤ/2ℤ`.

*Needs:* GrothendieckEulerForms exact structures; GeometricRepresentationCategories §R5.2; Mathlib
`CategoryTheory.Abelian.Ext`.

### 3.2 Ext-trivial ideals

**Projectively and injectively trivial morphisms** (intended `ExactStructure.projTrivialIdeal`,
`ExactStructure.injTrivialIdeal`). `𝒫_E(X, Y)` consists of the `f : X → Y` with
`Ext¹_E(f, W) = 0 : Ext¹_E(Y, W) → Ext¹_E(X, W)` for every `W`, and `ℐ_E(X, Y)` of the `f` with
`Ext¹_E(W, f) = 0` for every `W` ([INP, Def. 1.21 and Rem. 1.22]; [En, §A.2]; Lenzing-Zuazua,
§2). Both are
morphism ideals (`TauCeti.MorphismIdeal`), with quotients `E/𝒫` and `E/ℐ`. A morphism factoring
through a relative projective lies in `𝒫_E`, and `𝒫_E` is exactly the ideal of such morphisms when
`E` has enough relative projectives, so that `E/𝒫` is then the projective stable category; dually
for `ℐ_E`.

**Checks.**

- For the split exact structure every morphism is projectively and injectively trivial, so
  `E/𝒫 = E/ℐ = 0`.
- For `mod A` with its abelian structure, `𝒫` is the ideal of maps factoring through projectives,
  and `E/𝒫` is `TauCeti.ExactStructure.ProjectiveStableCategory`.
- In the category of finite abelian groups, which has no nonzero projectives, the identity of
  `ℤ/pℤ` is not projectively trivial, since `Ext¹(ℤ/pℤ, ℤ/pℤ) ≠ 0`.

*Needs:* 3.1's `Ext¹`; StablePeriodicCurved Layer 0; Tau Ceti `TauCeti.MorphismIdeal`,
`TauCeti.ExactStructure.ProjectiveStableCategory`.

### 3.3 Almost-split conflations

**Almost-split conflations** (intended `ExactStructure.IsAlmostSplitConflation`). A conflation `S`
with `ShortComplex.IsAlmostSplit S`. In a Krull-Schmidt exact category its end terms are
indecomposable, and an almost-split conflation ending at a given `Z` is unique up to isomorphism of
conflations; so is one starting at a given `X`.

**The extension-class criterion** (intended `isAlmostSplit_iff_ext1`). A conflation with
indecomposable end terms is almost split exactly when its class is nonzero and is killed by pushout
along every morphism out of its first term that is not a split monomorphism. For the abelian
structure this is the criterion through Mathlib's `extClass`, which becomes its case.

**Checks.**

- `0 → ℤ/2ℤ → ℤ/4ℤ → ℤ/2ℤ → 0` is almost split in `mod (ℤ/4ℤ)`.
- `0 → k → k[ε]/(ε²) → k → 0` is almost split in `mod (k[ε]/(ε²))`.
- A split conflation is never almost split, since its class is zero.

*Needs:* 3.1's `Ext¹`; 0.2's `IsKrullSchmidt`; Tau Ceti `ShortComplex.IsAlmostSplit`,
`TauCeti.IsLeftAlmostSplit`, `TauCeti.IsRightAlmostSplit`.

### 3.4 The functorial picture

**Right almost-split maps as projective covers** (intended `isRightAlmostSplit_iff_range_eq_rad`).
Let `E` be a Krull-Schmidt exact category and `Z` indecomposable. A morphism `g : Y → Z` is right
almost split exactly when the image of `(-, g) : (-, Y) → (-, Z)` is `rad(-, Z)`, so that
`(-, Y) → (-, Z) → S_Z → 0` is a projective presentation of `S_Z`, and `g` is minimal right almost
split exactly when `(-, Y) ↠ rad(-, Z)` is a projective cover in the sense of 1.5. The functor
`rad(-, Z)` is finitely generated when `S_Z` is finitely presented, but need not be finitely
presented when `E` lacks weak kernels. So `Z` ends a right almost-split morphism exactly when `S_Z`
is finitely presented, and a finitely presented functor is simple exactly when it is `S_Z` for an
indecomposable `Z` with `S_Z` finitely presented. A conflation `X ↪ Y ↠ Z` with `Z` non-projective is
almost split exactly when `0 → (-, X) → (-, Y) → (-, Z) → S_Z → 0` is a minimal projective
resolution of `S_Z`.

**Checks.**

- For `ℤ/4ℤ`, the almost-split sequence ending at `ℤ/2ℤ` is the minimal projective resolution of
  the simple functor at `ℤ/2ℤ`.
- For a projective indecomposable `P` in `mod A`, the inclusion of its radical is right almost
  split, and `(-, rad P) → rad(-, P)` is a projective cover.
- The identity of `Z` is not right almost split: its image is all of `(-, Z)`, not `rad(-, Z)`.

*Needs:* 1.5's projective covers; 3.3's almost-split conflations; 0.6's radical.

### 3.5 Auslander-Reiten duality and existence

**Auslander-Reiten duality** (intended `ExactStructure.ARDuality`). For an exact category that is
Hom-finite over `R`, Krull-Schmidt, and with every `Ext¹` of finite length over `R`, an
Auslander-Reiten duality is an equivalence `τ : E/𝒫 ≌ E/ℐ` together with isomorphisms
`Ext¹_E(Z, X) ≅ D_R ((E/ℐ)(X, τ Z))` natural in `X` and `Z`.

**Existence** (intended `exists_isAlmostSplitConflation_iff`). For such a category the following
are equivalent: (a) there is an almost-split conflation ending at every indecomposable object that is
not projective, and one starting at every indecomposable object that is not injective; (b) there is
an Auslander-Reiten duality. Then the almost-split conflation ending at `Z` is `τ Z ↪ Y ↠ Z`, and `τ`
is a bijection from the isomorphism classes of indecomposable non-projective objects to those of
indecomposable non-injective objects. The sources differ in their base. Over a field, for
extriangulated categories and without enough projectives or injectives, this is [INP, Thm. 3.6]
(Def. 3.4 for the duality, Prop. 3.7 for the one-sided form). Over a commutative Noetherian complete
local ring, in particular a local Artinian ring, [En, Prop. A.5] proves the objectwise equivalence
(an almost-split conflation ends at `Z` exactly when `D Ext¹(Z, -)` is representable), and [En, Thm.
A.9] the global one under enough projectives and injectives. For abelian categories over a
commutative Artinian ring it is Lenzing-Zuazua, Thm. 1.1. The target is proved over a local
Artinian ring by assembling [En, Prop. A.5] objectwise as in the proof of [INP, Thm. 3.6], with
`D_R` for the duality over a field. For a general commutative Artinian `R = ∏ Rᵢ` (2.1), the central
idempotents of `R` split an `R`-linear exact category into a finite product of `Rᵢ`-linear exact
categories, `D_R` is the product of the `D_{Rᵢ}`, and the theorem follows factorwise.

**Checks.**

- For `mod A` with `A` an Artin algebra, (b) holds (Layer 4), so almost-split sequences exist.
- For the split exact structure on a Krull-Schmidt category, every object is projective and
  injective, so (a) holds vacuously and `τ` is the functor between zero categories.
- For `R = k × k` and `E = mod (k × k)`, the category is the product of two copies of `mod k`, and
  the factorwise statement is the field case on each copy.

*Needs:* 3.2's Ext-trivial ideals; 3.3's almost-split conflations; 2.2's duality; 2.1's local
factors.

### Examples

`mod (ℤ/4ℤ)` with its abelian structure has the single almost-split sequence ending at `ℤ/2ℤ`; the
split exact structure on any Krull-Schmidt category has none.

### Dependencies

Layers 0, 1 and 2; GrothendieckEulerForms; StablePeriodicCurved Layer 0;
GeometricRepresentationCategories §R5.2.

## Layer 4: Auslander-Reiten theory of Artin algebras

### 4.1 The translate

**`τ` and `τ⁻`** (intended `ArtinAlgebra.translate`, `ArtinAlgebra.invTranslate`). For a finitely
generated module `M` over an Artin `R`-algebra, take a minimal projective presentation (projective
covers exist over Artinian rings, `TauCeti.exists_projectiveCover`), its transpose `Tr M`
(`TauCeti.AuslanderReitenTranspose`), and set `τ M = D_R (Tr M)` and `τ⁻ M = Tr (D_R M)`. Both are
finitely generated and independent of the presentation up to isomorphism; `τ M = 0` exactly when `M`
is projective; for indecomposable non-projective `M`, `τ M` is indecomposable and not injective, and
`τ⁻ (τ M) ≅ M` ([ARS, Ch. IV]). Over a field, `TauCeti.AuslanderReitenTranslate`
and the quiver translate `TauCeti.arTranslate` are this construction with `R = k`.

**Checks.**

- For `A = ℤ/p²ℤ`, `τ (ℤ/pℤ) ≅ ℤ/pℤ`.
- `τ A = 0`.
- For `T₂(k)`, `τ` sends the simple non-projective module to the simple projective module.

*Needs:* 2.2's duality; Tau Ceti `TauCeti.AuslanderReitenTranspose`, `TauCeti.exists_projectiveCover`.

### 4.2 The stable equivalence and the Auslander-Reiten formulas

**Stable equivalence** (intended `ArtinAlgebra.translateEquivalence`). `D_R` induces an
anti-equivalence between the projective stable category of `mod Aᵐᵒᵖ` and the injective stable
category of `mod A`. Composed with `TauCeti.stableTransposeEquivalence` it gives the equivalence
`τ : E/[P] ≌ E/[I]` for the abelian exact structure `E` on `mod A`.

**The Auslander-Reiten formulas** (intended `ArtinAlgebra.extEquivDualInjStable`,
`ArtinAlgebra.extEquivDualProjStable`). For finitely generated `M` and `N`, natural isomorphisms
`Ext¹_A(M, N) ≅ D_R (Hom_A(N, τ M) modulo maps factoring through injectives)` and
`Ext¹_A(M, N) ≅ D_R (Hom_A(τ⁻ N, M) modulo maps factoring through projectives)`. Over a field these
are [ASS, Thm. IV.2.13]. For Artin algebras, [ARS, Props. IV.4.5 and IV.4.6] prove the equalities of
lengths, and the functorial isomorphisms are stated at the end of [ARS, §IV.4] without proof; the
target is the natural isomorphism, proved by the argument of [ASS, Thm. IV.2.13] with `D_R`. With the stable equivalence, the first
makes `τ` an Auslander-Reiten duality for `mod A`, whose Ext-trivial quotients are the two stable
categories (3.2).

**Checks.**

- For `M` projective both sides vanish.
- For `A = ℤ/p²ℤ` and `M = N = ℤ/pℤ`, both sides have length 1.
- For `A = k` (semisimple), every module is projective and injective, and both sides vanish.

*Needs:* 4.1's translate; 3.2's Ext-trivial ideals; 3.5's definition of duality; Tau Ceti
`TauCeti.stableTransposeEquivalence`, `TauCeti.ExactStructure.ProjectiveStableCategory`;
StablePeriodicCurved Layer 0 for the injective stable category.

### 4.3 Almost-split sequences, source and sink maps

**Almost-split sequences** (`exists_isAlmostSplit`, in `Suggested.lean`). For every indecomposable
non-projective finitely generated module `M` there is an almost-split sequence `0 → τ M → Y → M → 0`
in `mod A`, unique up to isomorphism, and dually for every indecomposable non-injective module
([ARS, Thm. V.1.15]); this is 3.5 applied to `mod A`. Equivalently, every simple
contravariant functor on `mod A` is finitely presented, and dually. Over a field the existence
theorem of QuiverRepresentations 6E is its case `R = k`.

**Source and sink maps** (intended `exists_isMinimalRightAlmostSplit`,
`isIrreducibleMorphism_iff_exists_isMinimalRightAlmostSplit`). Every indecomposable finitely
generated module `M` has a minimal right almost-split map `Y → M` (for `M` projective, the inclusion
of its radical) and a minimal left almost-split map `M → Y'` (for `M` injective, the quotient by its
socle). A map `h : X → M` with `X ≠ 0` is irreducible exactly when there is `h' : X' → M` such that
`(h, h') : X ⊕ X' → M` is minimal right almost split.

**Checks.**

- For `ℤ/p²ℤ`, the almost-split sequence ending at `ℤ/pℤ` is `0 → ℤ/pℤ → ℤ/p²ℤ → ℤ/pℤ → 0`.
- For `T₂(k)`, the almost-split sequence has the projective-injective module as middle term.
- The sink map of the projective `ℤ/p²ℤ` over `ℤ/p²ℤ` is the inclusion `pℤ/p²ℤ → ℤ/p²ℤ`.

*Needs:* 3.5's existence; 4.2's formulas; 3.4's functorial picture; Tau Ceti
`TauCeti.IsIrreducibleMorphism`.

### Examples

`ℤ/p²ℤ`, `k[ε]/(ε²)` and `T₂(k)` are representation-finite with explicit almost-split sequences;
`ℤ/p²ℤ` is not an algebra over a field, and the first two are local.

### Dependencies

Layers 2 and 3; Tau Ceti's transpose and its stable equivalence.

## Layer 5: the valued Auslander-Reiten quiver

### 5.1 Irreducible-morphism bimodules and valuations

**`Irr(M, N)`** (intended `irrBimodule`, `valuation`). For objects `M` and `N` with local endomorphism
rings in a preadditive category, `Irr(M, N) = rad(M, N) / rad²(M, N)` is a bimodule over the division
rings `F_N = End N / rad (End N)` (acting by composition after) and `F_M = End M / rad (End M)`
(acting by composition before). For indecomposable finitely generated modules over an Artin algebra
it is finite-dimensional over each, and its two dimensions form the **valuation**
`(a_{MN}, b_{MN})`, with `a_{MN}` the dimension over `F_N` and `b_{MN}` over `F_M`.

**Checks.**

- For `ℤ/p²ℤ`, both arrows between `ℤ/pℤ` and `ℤ/p²ℤ` have valuation `(1, 1)`.
- For the `ℝ`-algebra `A` of upper triangular `2 × 2` matrices with diagonal entries in `ℝ` and `ℂ`
  and corner entry in `ℂ`, the successive valuations along the almost-split sequence are `(1, 2)`
  and `(2, 1)`, and the middle term has multiplicity 1; reversing the two dimensions would predict 2.
- Over an algebraically closed field the valuations are `(n, n)` with `n = dim_k Irr(M, N)`.

*Needs:* 0.6's radical and `rad²`; Tau Ceti `TauCeti.jacobsonRadicalSq`.

### 5.2 Valued translation quivers

**Valued translation quivers** (intended `ValuedTranslationQuiver`). A quiver whose arrows carry
pairs of positive integers, with a partial injection `τ` on vertices such that for every vertex `z`
in the domain of `τ` and every vertex `w`, there is an arrow `τ z → w` exactly when there is an arrow
`w → z`, and the valuation of `τ z → w` is that of `w → z` with the two entries exchanged ([ARS,
§VII.1], with Prop. VII.1.5 for the valuation under `τ`).

**Checks.**

- The quiver with one vertex, no arrows and empty `τ` is a valued translation quiver.
- The two-vertex quiver of `ℤ/p²ℤ` with `τ [ℤ/pℤ] = [ℤ/pℤ]` and both valuations `(1, 1)` is one.
- Giving the translated arrow the same valuation `(1, 2)` as the original arrow, instead of
  `(2, 1)`, violates the condition.

*Needs:* Mathlib `Quiver`.

### 5.3 The valued Auslander-Reiten quiver

**The quiver** (intended `valuedARQuiver A`). Vertices the isomorphism classes of indecomposable
finitely generated `A`-modules, an arrow `[M] → [N]` exactly when `Irr(M, N) ≠ 0`, labelled by its
valuation, with `τ` defined exactly on the non-projective vertices.

**Multiplicities** (intended `multiplicity_eq_valuation`). In the almost-split sequence
`0 → τ Z → Y → Z → 0`, the number of copies of an indecomposable `W` among the summands of `Y` equals
`b_{WZ}`, and also equals `a_{τZ,W}` ([ARS, Prop. VII.1.3]).

**The mesh** (intended `valuedARQuiver_isValuedTranslationQuiver`). `valuedARQuiver A` is a valued
translation quiver.

**Over a field.** For `A` over a field `k`, `dim_k Irr(M, N) = b_{MN} · dim_k F_M`; this recovers the
arrow counts of QuiverRepresentations 6F's `arQuiver k A`. When `F_M = F_N = k`, the valuation is
`(n, n)` with `n = dim_k Irr(M, N)`.

**Checks.**

- For `ℤ/p²ℤ`, the quiver has the two arrows `[ℤ/pℤ] → [ℤ/p²ℤ]` and `[ℤ/p²ℤ] → [ℤ/pℤ]`.
- For `T₂(k)` it is the mesh with three vertices and two arrows.
- For the real-complex triangular algebra of 5.1 it has an arrow whose valuation is not of the form
  `(n, n)`.

*Needs:* 5.1's valuations; 5.2's valued translation quivers; 4.3's almost-split sequences.

### Examples

The real-complex triangular algebra is the test case for valuations that are not symmetric.

### Dependencies

Layers 0 and 4.

## Layer 6: finiteness theorems

### 6.1 Representation-finite Artin algebras and the Harada-Sai lemma

**Representation-finite** (intended `IsRepresentationFinite A`). `mod A` has finitely many
isomorphism classes of indecomposable objects (`Skeleton` of the full subcategory of finitely
generated indecomposable modules is finite).

**The Harada-Sai lemma** (`chainComp_eq_zero_of_length_le`, in `Suggested.lean`, with the auxiliary
`chainComp`). Let `M₀, …, Mₙ` be indecomposable modules of length at most `b`, and
`fᵢ : Mᵢ₋₁ ⟶ Mᵢ` non-isomorphisms. If `n ≥ 2 ^ b - 1`, then `fₙ ∘ ⋯ ∘ f₁ = 0` ([ARS, Cor. VI.1.3], with
the technical bound in Lemma VI.1.2; [ASS, Lemma IV.5.2], with Example IV.5.3 showing that the bound
is best possible). Harada-Sai, Lemma 12, prove only that some composite vanishes. Consequently, if `A` is representation-finite
and every indecomposable has length at most `b`, then
`jacobsonRadicalIdeal (FGModuleCat A) ^ (2 ^ b - 1) = ⊥`.

**Checks.**

- For `b = 1`, a single non-isomorphism between simple modules is zero.
- For `B = k[ε]/(ε²)`, with `b = 2`, the chain `B → k → B` of two non-isomorphisms has nonzero
  composite `ε`, while every chain of `3 = 2² - 1` non-isomorphisms between `k` and `B` is zero.
- For the Kronecker algebra the lengths are unbounded, and no power of the radical of `mod A` is
  zero.

*Needs:* 0.6's `jacobsonRadicalIdeal`; Mathlib `Module.length`, `CategoryTheory.Indecomposable`.

### 6.2 Auslander's theorem and the first Brauer-Thrall conjecture

**Auslander's theorem** (intended `IsRepresentationFinite.of_component_length_le`). Let `A` be
connected (`0` and `1` are its only central idempotents) and let `𝒞` be a weakly connected component
of `valuedARQuiver A` (Mathlib's `Quiver.WeaklyConnectedComponent`). If the lengths of the modules in
`𝒞` are bounded, then `𝒞` is the whole quiver, and `A` is representation-finite ([ARS, Thm.
VI.1.4]; Auslander, *Representation theory of Artin algebras II*).

**The first Brauer-Thrall conjecture** (`finite_skeleton_of_length_le`, in `Suggested.lean`). If the
lengths of the indecomposable finitely generated `A`-modules are bounded, then `A` is
representation-finite (Roiter; [ARS, Cor. VI.1.5]).

**The infinite radical** (intended `rad_infty_eq_bot_iff`). `rad^∞ = ⨅ n, jacobsonRadicalIdeal
(FGModuleCat A) ^ n`, and `A` is representation-finite exactly when `rad^∞ = ⊥` (Auslander,
Representation theory of Artin algebras II).

**Connectedness.** For a connected representation-finite `A`, `valuedARQuiver A` is weakly
connected.

**Checks.**

- For `ℤ/p²ℤ`, the quiver is one component of bounded length, and the algebra is
  representation-finite.
- For `k × k`, which is not connected, the quiver has two components.
- For the Kronecker algebra, the preprojective component has unbounded lengths and is not the whole
  quiver, and `rad^∞ ≠ ⊥`.

*Needs:* 6.1's Harada-Sai lemma; 5.3's valued quiver; 4.3's almost-split sequences; Mathlib
`Quiver.WeaklyConnectedComponent`.

### Examples

`k[ε]/(ε²)` realizes the Harada-Sai bound for `b = 2` exactly; the Kronecker algebra is the
representation-infinite control.

### Dependencies

Layers 0, 4 and 5.

## Layer 7: Morita theory, global and dominant dimension, and the correspondences

### 7.1 Projectivization and Morita theory

**Projectivization** (intended `projectivizationEquiv`). For a finitely generated `A`-module `M` with
`Γ = Module.End A M`, `Hom_A(M, -)` is an equivalence from `add M` (direct summands of finite sums of
copies of `M`) to the finitely generated projective right `Γ`-modules, and `Hom_A(-, M)` is an
anti-equivalence from `add M` to the finitely generated projective left `Γ`-modules; both send `M` to
`Γ` ([ARS, Prop. II.2.1]). With 1.3, `mod (add M)` is the category of finitely presented
right `Γ`-modules. `Γ` is an Artin `R`-algebra, with Mathlib's scoped `ModuleCat.Algebra` instances.

**The double centralizer** (intended `doubleCentralizer`). If `M` is a generator of `mod A`, the
action map `A → Module.End Γ M` is a ring isomorphism.

**Morita theory for Artin algebras** (intended `isMoritaEquivalent_iff_nonempty_linearEquivalence`).
For a finitely generated projective generator `P` of `mod A`, 1.3 gives `mod A ≌` the finitely
presented right `Module.End A P`-modules, and `IsMoritaEquivalent R A (Module.End A P)ᵐᵒᵖ` follows
from Mathlib's `IsMoritaEquivalent.matrix` and Tau Ceti's `IsIdempotentElem.isMoritaEquivalent_corner`,
since `(Module.End A P)ᵐᵒᵖ ≅ e Matₙ(A) e` for a full idempotent `e`. Hence an `R`-linear equivalence
`mod A ≌ mod B` exists exactly when `IsMoritaEquivalent R A B`; one direction restricts the
equivalence of module categories (`CategoryTheory.Equivalence.finiteModulesEquivalence`). A Morita
equivalence of Artin algebras preserves projectives, injectives, projective-injectives,
indecomposables, minimal injective coresolutions, generator-cogenerators and additive generators;
so it preserves representation-finiteness, global dimension and dominant dimension.

**Checks.**

- For `M = A`, `Γ ≅ Aᵐᵒᵖ`, and the double centralizer is the identity of `A`.
- For `P = Aⁿ`, `Module.End A P ≅ Matₙ(A)ᵐᵒᵖ`, and the Morita equivalence is `IsMoritaEquivalent.matrix`.
- `k` and `k × k` are not Morita equivalent: `mod k` has one indecomposable up to isomorphism and
  `mod (k × k)` has two.

*Needs:* 1.3's progenerators; 0.5's additive generators; Mathlib `IsMoritaEquivalent`; Tau Ceti
`IsIdempotentElem.isMoritaEquivalent_corner`, `CategoryTheory.Equivalence.finiteModulesEquivalence`.

### 7.2 Global dimension

**Global dimension of a ring** (`leftGlobalDimension`, in `Suggested.lean`). For an arbitrary ring
`A`, the left global dimension is the supremum of the projective dimensions (Mathlib's
`CategoryTheory.projectiveDimension` in `ModuleCat A`) of all left `A`-modules, and the right global
dimension is the left global dimension of `Aᵐᵒᵖ`. On a commutative ring it is
PurityOfBranchLocus §0.3's `globalDimension`, by the same supremum
(`leftGlobalDimension_eq_globalDimension`, in `Suggested.lean`); one implementation serves both when
the library is built, and the commutative criteria and localization bounds of §0.3 are imported.

**Auslander's theorems** (`leftGlobalDimension_mulOpposite`, in `Suggested.lean`; intended
`leftGlobalDimension_eq_iSup_cyclic`, `leftGlobalDimension_eq_iSup_fg`,
`leftGlobalDimension_eq_projectiveDimension_quotient_jacobson`). The left global dimension is the
supremum over the cyclic modules `A ⧸ I`; for a left Noetherian ring it is the supremum over the
finitely generated modules; for a ring that is left and right Noetherian the left and right global
dimensions agree; and for a semiprimary ring, in particular an Artin algebra, both equal the
projective dimension of `A ⧸ J(A)` (Auslander, On the dimension of modules and algebras III). For
Artin algebras the global dimension is written `gl.dim`.

**Checks.**

- The zero ring has global dimension `⊥`, since a zero object has projective dimension `⊥`.
- A field has global dimension `0`, and `ℤ` has global dimension `1`.
- `k[ε]/(ε²)` has infinite global dimension: `k` has the periodic resolution
  `⋯ → B → B → k → 0` by multiplication by `ε`.

*Needs:* Mathlib `CategoryTheory.projectiveDimension`, `IsNoetherianRing`, `IsSemiprimaryRing`;
PurityOfBranchLocus §0.3.

### 7.3 Dominant dimension

**Dominant dimension** (intended `dominantDimension`; its bound `≥ 2` is
`HasProjectiveInjectiveCopresentation`, in `Suggested.lean`). For an Artin algebra `Γ` with minimal
injective coresolution `0 → Γ → I⁰ → I¹ → ⋯` of the left regular module (2.3), `dom.dim Γ ≥ n` when
`I⁰, …, Iⁿ⁻¹` are projective; `dom.dim Γ` is the supremum of such `n` in `ℕ∞`. For `n = 2` this is
an injective copresentation `0 → Γ → I⁰ → I¹` by finitely generated projective-injective modules.

**Checks.**

- `k[ε]/(ε²)` is self-injective, so its dominant dimension is infinite.
- For the path algebra of `• → •` (that is, `T₂(k)`), the dominant dimension is 1: the injective
  hull of the simple projective module is projective-injective, and its cokernel, the other simple
  module, is injective but not projective.
- For `B = k[ε]/(ε²)`, `End_B(B ⊕ k)` has dominant dimension 2.

*Needs:* 2.3's minimal injective coresolutions; Mathlib `CategoryTheory.Projective`,
`CategoryTheory.Injective`.

### 7.4 The Morita-Tachikawa correspondence

**Generator-cogenerators** (`IsGeneratorCogenerator`, in `Suggested.lean`). Every finitely
generated indecomposable projective and every finitely generated indecomposable injective module is
a direct summand of `M`.

**Forward** (`hasProjectiveInjectiveCopresentation_end`, in `Suggested.lean`). If `M` is a
generator-cogenerator of `mod A`, then `dom.dim (Module.End A M) ≥ 2`.

**Converse** (`exists_ringEquiv_end_of_hasProjectiveInjectiveCopresentation`, in `Suggested.lean`).
For an Artin algebra `Γ` with `dom.dim Γ ≥ 2`, let `Q` be the sum of the indecomposable
projective-injective left `Γ`-modules, one of each isomorphism class, and `B = Module.End Γ Q`; then
`Q` is a generator-cogenerator of `mod B`, and the action map `Γ → Module.End B Q` is a ring
isomorphism.

**The correspondence** (`isMoritaEquivalent_of_ringEquiv_end`, in `Suggested.lean`). Pairs `(A, M)`
with `M` a generator-cogenerator of `mod A` are identified when an `R`-linear equivalence
`mod A ≌ mod A'` carries `add M` onto `add M'`. The constructions `(A, M) ↦ Module.End A M` and
`Γ ↦ (Module.End Γ Q, Q)` are inverse bijections between these classes and the isomorphism classes
of Artin algebras of dominant dimension at least two: the converse gives surjectivity, and if the
endomorphism rings of two generator-cogenerators are isomorphic then the algebras are Morita
equivalent (Müller; Tachikawa).

**Checks.**

- For `M = A ⊕ D_R A`, a generator-cogenerator, `dom.dim (Module.End A M) ≥ 2`.
- For a self-injective `A`, `M = A` is a generator-cogenerator, and `Γ ≅ Aᵐᵒᵖ` has infinite
  dominant dimension.
- `T₂(k)` has dominant dimension 1, so it is not the endomorphism ring of a generator-cogenerator.

*Needs:* 7.1's projectivization and double centralizer; 7.3's dominant dimension; 2.3's
injective hulls.

### 7.5 The Auslander correspondence

**Forward** (`hasProjectiveDimensionLE_two`, in `Suggested.lean`; `IsAdditiveGenerator`, in
`Suggested.lean`). If `M` is an additive generator of `mod A` (0.5; it exists exactly when `A` is
representation-finite), then `add M = mod A`, so the finitely presented right `Γ`-modules form
`mod (mod A)` and have projective dimension at most two (1.4); so the right global dimension of
`Γ = Module.End A M` is at most two, and so is its left global dimension (7.2). Besides,
`dom.dim Γ ≥ 2` (7.4).

**Converse** (`exists_isAdditiveGenerator_ringEquiv_end`, in `Suggested.lean`). If
`gl.dim Γ ≤ 2 ≤ dom.dim Γ`, the generator-cogenerator `Q` of 7.4 is an additive generator of
`mod B`. So the Morita-Tachikawa bijection restricts to a bijection between Morita classes of
representation-finite Artin algebras and Morita classes of **Auslander algebras**, the Artin
algebras with `gl.dim Γ ≤ 2 ≤ dom.dim Γ` ([ARS, Thm. VI.5.7], with Props. VI.5.4 and VI.5.6;
Auslander, *Representation dimension of Artin algebras*).

**Checks.**

- For `B = k[ε]/(ε²)` and `M = B ⊕ k`, `End_B(M)` has dimension 5 over `k`, global dimension 2 and
  dominant dimension 2, and the converse reconstructs `B`.
- `B` itself has infinite dominant dimension but infinite global dimension, so dominant dimension
  alone does not give the conclusion.
- For a semisimple `A` and an additive generator `M`, `Module.End A M` is semisimple, of global
  dimension 0; and for `Mat₂(k) = End_k(k²)`, every module is projective, so projective dimensions
  are 0.

*Needs:* 7.4's correspondence; 1.4's projective dimension bound; 0.5's additive generators; 7.2's
global dimension.

### Examples

`End_B(B ⊕ k)` for `B = k[ε]/(ε²)`, of dimension 5, and `End_A(ℤ/p²ℤ ⊕ ℤ/pℤ)` for `A = ℤ/p²ℤ`, are
Auslander algebras, with global dimension 2 and dominant dimension 2. For the zero algebra every
module is zero, and the global dimension is `⊥`.

### Dependencies

Layers 0, 1 and 2; PurityOfBranchLocus §0.3.

## References

- [ASS] I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Vol. 1, London Mathematical Society Student Texts 65, Cambridge University Press
  (2006).
- M. Auslander, *Coherent functors*, Proceedings of the Conference on Categorical Algebra (La Jolla,
  1965), Springer (1966), 189–231.
- M. Auslander, *On the dimension of modules and algebras III. Global dimension*, Nagoya Math. J. 9
  (1955), 67–77.
- M. Auslander, *Representation dimension of Artin algebras*, Queen Mary College Mathematics Notes,
  London (1971).
- M. Auslander, *Representation theory of Artin algebras II*, Comm. Algebra 1 (1974), 269–310.
- [ARS] M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  Studies in Advanced Mathematics 36, Cambridge University Press (1995).
- S. U. Chase, *Direct products of modules*, Trans. Amer. Math. Soc. 97 (1960), 457–473.
- [En] H. Enomoto, *Classifications of exact structures and Cohen-Macaulay-finite algebras*, Adv.
  Math. 335 (2018), 838–877, arXiv:1705.02163.
- P. Freyd, *Representations in abelian categories*, Proceedings of the Conference on Categorical
  Algebra (La Jolla, 1965), Springer (1966), 95–120.
- M. Harada, Y. Sai, *On categories of indecomposable modules I*, Osaka J. Math. 7 (1970), 323–344.
- M. Hoshino, *On dominant dimension of Noetherian rings*, Osaka J. Math. 26 (1989), 275–280.
- [INP] O. Iyama, H. Nakaoka, Y. Palu, *Auslander-Reiten theory in extriangulated categories*,
  arXiv:1805.03776.
- [Kr] H. Krause, *Krull-Schmidt categories and projective covers*, Expo. Math. 33 (2015), 535–549,
  arXiv:1410.2822.
- H. Lenzing, R. Zuazua, *Auslander-Reiten duality for abelian categories*, Bol. Soc. Mat. Mexicana
  (3) 10 (2004), 169–177.
- E. Matlis, *Injective modules over Noetherian rings*, Pacific J. Math. 8 (1958), 511–528.
- B. J. Müller, *The classification of algebras by dominant dimension*, Canad. J. Math. 20 (1968),
  398–409.
- A. V. Roiter, *Unboundedness of the dimensions of the indecomposable representations of an algebra
  which has infinitely many indecomposable representations*, Izv. Akad. Nauk SSSR Ser. Mat. 32
  (1968), 1275–1282.
- H. Tachikawa, *Quasi-Frobenius Rings and Generalizations*, Lecture Notes in Mathematics 351,
  Springer (1973).
- N. Yoneda, *On Ext and exact sequences*, J. Fac. Sci. Univ. Tokyo Sect. I 8 (1960), 507–576.
