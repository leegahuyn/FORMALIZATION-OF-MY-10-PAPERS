import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineLineDivisorChartSections
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSkyscraperNaturality
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorCyclePullback

/-!
# Étale restriction of the actual divisor-sheaf charts

The finite divisor associated to a section restricts by contraction of
height-one primes. The calculation uses the geometric skyscraper
products and hence applies to the native divisor sheaf.
-/

namespace ManuscriptAudit.AffineLineDivisorSheaf

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections IsDedekindDomain
open AffineLineRationalClosedPoints AffineEtaleClosedPoints

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K B : Type) [Field K] [IsAlgClosed K] [CommRing B] [IsDomain B]
  [Algebra (Polynomial K) B] [Algebra.Etale (Polynomial K) B]

private abbrev A := Polynomial K

private abbrev componentSections (p : HeightOneSpectrum (A K)) :=
  (skyscraper K ((closedPointEquiv K).symm p)).obj.obj
      (op (algebraEtaleObject (A K) B))

private abbrev familySections :=
  Π₀ p : HeightOneSpectrum (A K), componentSections K B p

private theorem chartSectionsEquiv_coordinate (d : familySections K B)
    (p : HeightOneSpectrum (A K))
    (q : {q : HeightOneSpectrum B // comap (A K) B q = p}) :
    chartSectionsEquiv K B d q.val = chartComponentEquiv K B p (d p) q := by
  let e := cyclesByBasePoint (A K) B
  let s := DFinsupp.mapRange.addEquiv (chartComponentEquiv K B) d
  have he : e (chartSectionsEquiv K B d) = s := e.apply_symm_apply s
  rw [← cyclesByBasePoint_apply (A K) B (chartSectionsEquiv K B d) p q]
  change e (chartSectionsEquiv K B d) p q = _
  rw [he]
  rfl

variable (C : Type) [CommRing C] [IsDomain C]
  [Algebra (A K) C] [Algebra.Etale (A K) C] [Algebra B C]
  [IsScalarTower (A K) B C] [Algebra.Etale B C]

private abbrev étaleMap :=
  algebraEtaleMap (IsScalarTower.toAlgHom (A K) B C)

/-- The affine-site arrow associated to the displayed algebra map. -/
def chartArrow : chartObject K C ⟶ chartObject K B :=
  (Scheme.AffineEtale.Spec (X K)).preimage (étaleMap K B C)

private theorem chartArrow_map :
    (Scheme.AffineEtale.Spec (X K)).map (chartArrow K B C) = étaleMap K B C :=
  (Scheme.AffineEtale.Spec (X K)).map_preimage _

private theorem chartComponentEquiv_restrict (p : HeightOneSpectrum (A K))
    (x : componentSections K B p)
    (q : {q : HeightOneSpectrum C // comap (A K) C q = p}) :
    chartComponentEquiv K C p
      ((skyscraper K ((closedPointEquiv K).symm p)).obj.map (étaleMap K B C).op x) q =
    chartComponentEquiv K B p x (contractFiber (A K) B C p q) := by
  let a := (closedPointEquiv K).symm p
  letI : Algebra (A K) K := (Polynomial.evalRingHom a).toAlgebra
  have hp : closedPoint K a = p := (closedPointEquiv K).apply_symm_apply p
  have hs : (Spec.map (CommRingCat.ofHom (algebraMap (A K) K))
      (default : Spec (CommRingCat.of K))).asIdeal = p.asIdeal :=
    (congrArg PrimeSpectrum.asIdeal (rationalPoint_default K a)).trans
      (congrArg HeightOneSpectrum.asIdeal hp)
  have hK : Function.Surjective (algebraMap (A K) K) := by
    intro z
    exact ⟨Polynomial.C z, Polynomial.eval_C⟩
  let M := AddCommGrpCat.of ℤ
  let F := (skyscraper K a).obj
  let e := rationalSkyscraperHeightOneIso (A K) B K p hs hK M
  let e' := rationalSkyscraperHeightOneIso (A K) C K p hs hK M
  have h : F.map (étaleMap K B C).op ≫ e'.hom =
      e.hom ≫ Pi.map' (contractFiber (A K) B C p) (fun _ ↦ 𝟙 M) :=
    rationalSkyscraperHeightOneIso_naturality (A K) B C K p hs hK M
  have hπ := congrArg (fun m ↦ m ≫ Pi.π
    (fun _ : {q : HeightOneSpectrum C // comap (A K) C q = p} ↦ M) q) h
  simp only [Category.assoc, Pi.map'_comp_π, Category.comp_id] at hπ
  change Concrete.productEquiv _ (e'.hom (F.map (étaleMap K B C).op x)) q =
    Concrete.productEquiv _ (e.hom x) (contractFiber (A K) B C p q)
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply]
  exact ConcreteCategory.congr_hom hπ x

set_option maxHeartbeats 1400000 in
/-- The divisor coordinates of an actual affine étale section restrict
by the true pullback on finite height-one cycles. -/
theorem chartSectionsEquiv_restrict (d : familySections K B) :
    chartSectionsEquiv K C ((affineDivisorSheaf K).obj.map (chartArrow K B C).op d) =
      AffineEtaleClosedPoints.pullback B C (chartSectionsEquiv K B d) := by
  apply Finsupp.ext
  intro q
  let p := comap (A K) C q
  let q' : {r : HeightOneSpectrum C // comap (A K) C r = p} := ⟨q, rfl⟩
  let r : familySections K C := (affineDivisorSheaf K).obj.map (chartArrow K B C).op d
  have hr : r p = (skyscraper K ((closedPointEquiv K).symm p)).obj.map (étaleMap K B C).op (d p) := by
    let G := Scheme.AffineEtale.Spec (X K)
    change (skyscraper K ((closedPointEquiv K).symm p)).obj.map
      ((G.map (chartArrow K B C)).op) (d p) = _
    erw [chartArrow_map] <;> rfl
  calc
    _ = chartComponentEquiv K C p (r p) q' := chartSectionsEquiv_coordinate K C r p q'
    _ = chartComponentEquiv K B p (d p) (contractFiber (A K) B C p q') := by
      rw [hr]
      exact chartComponentEquiv_restrict K B C p (d p) q'
    _ = chartSectionsEquiv K B d (comap B C q) :=
      (chartSectionsEquiv_coordinate K B d p (contractFiber (A K) B C p q')).symm
    _ = _ := rfl

end

end ManuscriptAudit.AffineLineDivisorSheaf

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineLineDivisorSheaf.chartSectionsEquiv_restrict
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
