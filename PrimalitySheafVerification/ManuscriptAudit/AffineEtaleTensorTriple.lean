import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleMorphismLimits
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleTensorOverlap
import PrimalitySheafVerification.ManuscriptAudit.KummerAffineCohomology

/-! Pair and triple overlaps of one actual affine étale chart. -/

namespace ManuscriptAudit.AffineEtaleTensorTriple

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TensorProduct
open AffineEtaleTensorOverlap UnitCocycleTensor

noncomputable section

attribute [local instance] doubleEtale tripleEtale

variable (R B : Type) [CommRing R] [CommRing B] [Algebra R B] [Algebra.Etale R B]

private abbrev U := ofAlgebra R B
private abbrev D := ofAlgebra R (B ⊗[R] B)
private abbrev E := ofAlgebra R (B ⊗[R] (B ⊗[R] B))
private abbrev T := baseObject R
private abbrev hT : IsTerminal (T R) :=
  KummerAffineCohomology.affineTerminal_isTerminal (CommRingCat.of R)

private def tripleFirst : E R B ⟶ U R B :=
  ofAlgHom (Algebra.TensorProduct.includeLeft : B →ₐ[R] B ⊗[R] (B ⊗[R] B))

private theorem coord_ext {U' V' : (Spec (CommRingCat.of R)).AffineEtale} {f g : U' ⟶ V'}
    (h : ∀ b : V'.left.unop, f.left.unop.hom b = g.left.unop.hom b) : f = g := by
  apply MorphismProperty.CostructuredArrow.Hom.ext
  apply Quiver.Hom.unop_inj
  exact CommRingCat.hom_ext (RingHom.ext h)

private theorem p12_first : projection12 R B ≫ firstProjection R B = tripleFirst R B := by
  apply coord_ext R
  intro b
  let c : B := b
  change pull12 R B (c ⊗ₜ[R] (1 : B)) = c ⊗ₜ[R] (1 : B ⊗[R] B)
  simp only [pull12, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

private theorem p13_first : projection13 R B ≫ firstProjection R B = tripleFirst R B := by
  apply coord_ext R
  intro b
  let c : B := b
  change pull13 R B (c ⊗ₜ[R] (1 : B)) = c ⊗ₜ[R] (1 : B ⊗[R] B)
  simp only [pull13, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]

private theorem p12_second :
    projection12 R B ≫ secondProjection R B = projection23 R B ≫ firstProjection R B := by
  apply coord_ext R
  intro b
  let c : B := b
  change pull12 R B ((1 : B) ⊗ₜ[R] c) = pull23 R B (c ⊗ₜ[R] (1 : B))
  simp only [pull12, pull23, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.includeLeft_apply, Algebra.TensorProduct.includeRight_apply]

private theorem p13_second :
    projection13 R B ≫ secondProjection R B = projection23 R B ≫ secondProjection R B := by
  apply coord_ext R
  intro b
  let c : B := b
  change pull13 R B ((1 : B) ⊗ₜ[R] c) = pull23 R B ((1 : B) ⊗ₜ[R] c)
  simp only [pull13, pull23, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.includeRight_apply]

set_option backward.isDefEq.respectTransparency false in
private theorem triple_isPullback :
    IsPullback (tripleFirst R B) (projection23 R B)
      (coverArrow R B) (coverArrow R (B ⊗[R] B)) := by
  let X := Spec (CommRingCat.of R)
  let F := Scheme.AffineEtale.Spec X ⋙ Scheme.Etale.forget X ⋙ Over.forget X
  apply IsPullback.of_map_of_faithful F
  exact isPullback_SpecMap_of_isPushout _ _ _ _
    ⟨⟨(CommRingCat.pushoutCocone R B (B ⊗[R] B)).condition⟩,
      ⟨CommRingCat.pushoutCoconeIsColimit R B (B ⊗[R] B)⟩⟩

variable {W V : (Spec (CommRingCat.of R)).AffineEtale}

/-- The actual arrow to the tensor-square overlap induced by any two restrictions. -/
def pair (a b : W ⟶ U R B) : W ⟶ D R B :=
  (double_isPullback R B).lift a b ((hT R).hom_ext _ _)

@[simp] theorem pair_first (a b : W ⟶ U R B) :
    pair R B a b ≫ firstProjection R B = a :=
  (double_isPullback R B).lift_fst _ _ _

@[simp] theorem pair_second (a b : W ⟶ U R B) :
    pair R B a b ≫ secondProjection R B = b :=
  (double_isPullback R B).lift_snd _ _ _

theorem pair_comp (k : V ⟶ W) (a b : W ⟶ U R B) :
    k ≫ pair R B a b = pair R B (k ≫ a) (k ≫ b) := by
  apply (double_isPullback R B).hom_ext <;> simp [Category.assoc]

/-- The actual arrow to the tensor-cube overlap induced by three restrictions. -/
def triple (a b c : W ⟶ U R B) : W ⟶ E R B :=
  (triple_isPullback R B).lift a (pair R B b c) ((hT R).hom_ext _ _)

private theorem triple_first (a b c : W ⟶ U R B) :
    triple R B a b c ≫ tripleFirst R B = a :=
  (triple_isPullback R B).lift_fst _ _ _

@[simp] theorem triple_23 (a b c : W ⟶ U R B) :
    triple R B a b c ≫ projection23 R B = pair R B b c :=
  (triple_isPullback R B).lift_snd _ _ _

@[simp] theorem triple_12 (a b c : W ⟶ U R B) :
    triple R B a b c ≫ projection12 R B = pair R B a b := by
  apply (double_isPullback R B).hom_ext
  · simp only [Category.assoc, p12_first, triple_first, pair_first]
  · rw [Category.assoc, p12_second, ← Category.assoc, triple_23, pair_first, pair_second]

@[simp] theorem triple_13 (a b c : W ⟶ U R B) :
    triple R B a b c ≫ projection13 R B = pair R B a c := by
  apply (double_isPullback R B).hom_ext
  · simp only [Category.assoc, p13_first, triple_first, pair_first]
  · rw [Category.assoc, p13_second, ← Category.assoc, triple_23, pair_second, pair_second]

end

end ManuscriptAudit.AffineEtaleTensorTriple

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  for name in [``ManuscriptAudit.AffineEtaleTensorTriple.pair_comp,
      ``ManuscriptAudit.AffineEtaleTensorTriple.triple_12,
      ``ManuscriptAudit.AffineEtaleTensorTriple.triple_13,
      ``ManuscriptAudit.AffineEtaleTensorTriple.triple_23] do
    let ax ← collectAxioms name
    let bad := ax.filter fun n => !allowed.contains n
    unless bad.isEmpty do
      throwError m!"{name} depends on unexpected axioms {bad}"
    logInfo m!"{name} uses {ax}"
