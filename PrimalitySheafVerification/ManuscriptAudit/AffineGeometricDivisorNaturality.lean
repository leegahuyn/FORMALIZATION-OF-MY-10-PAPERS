import Lean.Elab.BuiltinEvalCommand
import Lean.Util.CollectAxioms
import PrimalitySheafVerification.ManuscriptAudit.AffineGeometricDivisorSections
import PrimalitySheafVerification.ManuscriptAudit.AffineEtaleSkyscraperNaturality
import PrimalitySheafVerification.ManuscriptAudit.EtaleDivisorCyclePullback

/-!
# Étale restriction of the actual divisor-sheaf charts

The finite divisor associated to a section restricts by contraction of
height-one primes. The calculation uses the geometric skyscraper
products and hence applies to the native divisor sheaf.
-/

namespace ManuscriptAudit.AffineGeometricDivisorNaturality

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open GenericEtaleUnitSections IsDedekindDomain
open AffineEtaleClosedPoints AffineGeometricDivisorSheaf AffineGeometricDivisorSections

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable (K A B : Type) [Field K] [IsAlgClosed K] [CommRing A] [IsDedekindDomain A]
  [Algebra K A] [Algebra.FiniteType K A] [CommRing B] [IsDomain B]
  [Algebra A B] [Algebra.Etale A B]

private abbrev componentSections (p : HeightOneSpectrum A) :=
  (skyscraper K A p).obj.obj
      (op (algebraEtaleObject A B))

private abbrev familySections :=
  Π₀ p : HeightOneSpectrum A, componentSections K A B p

private theorem chartSectionsEquiv_coordinate (d : familySections K A B)
    (p : HeightOneSpectrum A)
    (q : {q : HeightOneSpectrum B // comap A B q = p}) :
    chartSectionsEquiv K A B d q.val = chartComponentEquiv K A B p (d p) q := by
  let e := cyclesByBasePoint A B
  let s := DFinsupp.mapRange.addEquiv (chartComponentEquiv K A B) d
  have he : e (chartSectionsEquiv K A B d) = s := e.apply_symm_apply s
  rw [← cyclesByBasePoint_apply A B (chartSectionsEquiv K A B d) p q]
  change e (chartSectionsEquiv K A B d) p q = _
  rw [he]
  rfl

variable (C : Type) [CommRing C] [IsDomain C]
  [Algebra A C] [Algebra.Etale A C] [Algebra B C]
  [IsScalarTower A B C] [Algebra.Etale B C]

private abbrev étaleMap :=
  algebraEtaleMap (IsScalarTower.toAlgHom A B C)

/-- The affine-site arrow associated to the displayed algebra map. -/
def chartArrow : chartObject A C ⟶ chartObject A B :=
  (Scheme.AffineEtale.Spec (X A)).preimage (étaleMap A B C)

private theorem chartArrow_map :
    (Scheme.AffineEtale.Spec (X A)).map (chartArrow A B C) = étaleMap A B C :=
  (Scheme.AffineEtale.Spec (X A)).map_preimage _

private theorem chartComponentEquiv_restrict (p : HeightOneSpectrum A)
    (x : componentSections K A B p)
    (q : {q : HeightOneSpectrum C // comap A C q = p}) :
    chartComponentEquiv K A C p
      ((skyscraper K A p).obj.map (étaleMap A B C).op x) q =
    chartComponentEquiv K A B p x (contractFiber A B C p q) := by
  let g := pointAlgHom K A p
  letI : Algebra A K := g.toRingHom.toAlgebra
  have hs : (Spec.map (CommRingCat.ofHom (algebraMap A K))
      (default : Spec (CommRingCat.of K))).asIdeal = p.asIdeal :=
    congrArg PrimeSpectrum.asIdeal (pointMap_default K A p)
  have hK : Function.Surjective (algebraMap A K) := by
    intro z
    exact ⟨algebraMap K A z, g.commutes z⟩
  let M := AddCommGrpCat.of ℤ
  let F := (skyscraper K A p).obj
  let e := rationalSkyscraperHeightOneIso A B K p hs hK M
  let e' := rationalSkyscraperHeightOneIso A C K p hs hK M
  have h : F.map (étaleMap A B C).op ≫ e'.hom =
      e.hom ≫ Pi.map' (contractFiber A B C p) (fun _ ↦ 𝟙 M) :=
    rationalSkyscraperHeightOneIso_naturality A B C K p hs hK M
  have hπ := congrArg (fun m ↦ m ≫ Pi.π
    (fun _ : {q : HeightOneSpectrum C // comap A C q = p} ↦ M) q) h
  simp only [Category.assoc, Pi.map'_comp_π, Category.comp_id] at hπ
  change Concrete.productEquiv _ (e'.hom (F.map (étaleMap A B C).op x)) q =
    Concrete.productEquiv _ (e.hom x) (contractFiber A B C p q)
  rw [Concrete.productEquiv_apply_apply, Concrete.productEquiv_apply_apply]
  exact ConcreteCategory.congr_hom hπ x

set_option maxHeartbeats 1400000 in
/-- The divisor coordinates of an actual affine étale section restrict
by the true pullback on finite height-one cycles. -/
theorem chartSectionsEquiv_restrict (d : familySections K A B) :
    chartSectionsEquiv K A C ((affineDivisorSheaf K A).obj.map (chartArrow A B C).op d) =
      AffineEtaleClosedPoints.pullback B C (chartSectionsEquiv K A B d) := by
  apply Finsupp.ext
  intro q
  let p := comap A C q
  let q' : {r : HeightOneSpectrum C // comap A C r = p} := ⟨q, rfl⟩
  let r : familySections K A C := (affineDivisorSheaf K A).obj.map (chartArrow A B C).op d
  have hr : r p = (skyscraper K A p).obj.map (étaleMap A B C).op (d p) := by
    let G := Scheme.AffineEtale.Spec (X A)
    change (skyscraper K A p).obj.map
      ((G.map (chartArrow A B C)).op) (d p) = _
    erw [chartArrow_map] <;> rfl
  calc
    _ = chartComponentEquiv K A C p (r p) q' := chartSectionsEquiv_coordinate K A C r p q'
    _ = chartComponentEquiv K A B p (d p) (contractFiber A B C p q') := by
      rw [hr]
      exact chartComponentEquiv_restrict K A B C p (d p) q'
    _ = chartSectionsEquiv K A B d (comap B C q) :=
      (chartSectionsEquiv_coordinate K A B d p (contractFiber A B C p q')).symm
    _ = _ := rfl

end

end ManuscriptAudit.AffineGeometricDivisorNaturality

open Lean Elab Command in
run_cmd do
  let allowed : List Name := [``propext, ``Classical.choice, ``Quot.sound]
  let name := ``ManuscriptAudit.AffineGeometricDivisorNaturality.chartSectionsEquiv_restrict
  let dependencies ← collectAxioms name
  let unexpected := dependencies.filter fun axiomName => !allowed.contains axiomName
  unless unexpected.isEmpty do
    throwError m!"{name} depends on unexpected axioms {unexpected}"
  logInfo m!"{name} uses {dependencies}"
