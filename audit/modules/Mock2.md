# Mock2.lean 감사 보고서

대상 파일: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Mock2.lean` (26,607줄, `namespace Mock2`)
태그: `formalization-final-authority-2026-08-21` (HEAD `8f7e861f`)
감사자: 13명 병렬 감사자 중 Mock2 담당. 1–26,607줄을 모두 읽음(커버리지 기록은 끝에 있음).

선언 통계(`decls_cls.json`, file=`Mock2`): 선언 2,404개. theorem 1,454, def 640, structure 147, abbrev 131, instance 21, inductive 5, class 4, example 2. 이 중 `Certificate`라는 이름의 structure가 64개(2,306줄), `*_certificate`/`checklist_*` 형태의 theorem·def가 84개(1,580줄)다. `:= rfl` 한 줄짜리 theorem은 342개, accessor 증명은 48개, 한 줄 trivial tactic 증명은 367개(25%)다. 24,613–26,603줄은 `#print axioms` 1,989줄이 전부다.

---

## 1. 목적과 논문 대응

- 대상 논문: Lee Ga Hyun, *"Global Poincaré Matching and Kloosterman-Compatible Test Kernels for Half-Integral Weight Mock-Theta Gauge Objects"* (헤더 1–18줄).
- 헤더는 이 논문이 "압도적으로 해석적/스펙트럼적"이라고 직접 밝힌다. 가중 automorphic Sobolev 공간, 반정수 Kuznetsov/Kloosterman, scattering matrix, Rankin–Selberg, mass gap이 그 내용이다. Mock2는 이 중 "초등적이고 검증 가능한 부분"만 다룬다. 해석적 부분은 `Mock2_Advanced.lean`이 맡는다고 적혀 있다(11–18줄).
- 이 파일이 형식화했다고 주장하는 논문 항목(20–397줄 §-map과 24,163–24,540줄 `PaperMap.traceRow`)은 다음과 같다.
  Definition 11–18, Lemma 6.1, Proposition 14–21, (6.2)·(6.12)·(6.13)·(6.14)·(6.18), Remark 6.9, Theorem 5.1(감사용), checklist §4.6–§11.2.
- 자체 분류(`PaperMap.classification`, 24,232줄): Prop 14, 15, 20은 `paperAssumption`이고 나머지 14개 항목은 `complete`다. 모든 행의 `build := .deferredToUser`이다(24,482줄의 `traceRow_build`가 이를 정리로 고정해 둠).

## 2. 헤드라인 정리 목록

| # | 줄 | Lean 이름 | 내용(요약) | 상태 |
|---|---|---|---|---|
| 1 | 2073 | `prop21_exact_sequence` | `ShortExact5 M (Pk p k)`: `0→(M)∩(N)→ℤ→ℤ/M×ℤ/N→ℤ/gcd→0`의 각 위치 exactness | U(초등) |
| 2 | 2309 | `Prop21StandardSequence.standardDiagram_certificate` | `Ab`의 `ShortComplex` 4개가 모두 `.Exact` | U |
| 3 | 2434 | `PhiCokernel.equivZMod` | 실제 몫 cokernel `≃+ ZMod (gcd M N)` (제1 동형정리) | U |
| 4 | 5057 / 5103 / 5246 | `Tor1ZDerivedComparison.mathlibTor1ZIsoCyclicModel`, `mathlibTor1ZPrimePowerCanonicalEquiv`, `prop21ActualTor_certificate` | **Mathlib의 실제 `CategoryTheory.Tor' (ModuleCat ℤ) 1`(ZMod M, ZMod N)**이 `ker(×M on ZMod N)` 및 `ZMod (p^min(v_p M,k))`과 동형 | U(진짜) |
| 5 | 3078 | `Thickness.prop21_primePower_group_cardinality` | `Nat.card (ZMod (gcd M p^k)) = p^min(v_p M, k)` | U |
| 6 | 9595 | `Definition11.originalPi_not_wellDefined` | 논문의 `π([τ])=|e^{2πiτ}|`는 `Γ(2)\ℍ`로 내려가지 않음(`[[1,0],[2,1]]` 반례) | U(반증) |
| 7 | 21662 / 21628 | `no_gamma2_sends_infinity_to_zero`, `no_qParameter_outside_unitDisk` | Γ(2)는 ∞를 0으로 보내지 못함. ℍ 위의 q는 항상 \|q\|<1 | U(반증, 짧음) |
| 8 | 22443 | `Proposition14.flatTransport_not_unique_from_flatness` | flatness만으로는 transport가 유일하지 않음(부호 gauge 반례) | U(반증) |
| 9 | 16605 / 16622 | `Definition15Geometry.EtaHalfWeight.branch`, `.multiplier` | Dedekind η로 weight-½ branch와 multiplier를 실제로 구성 | U(실질) |
| 10 | 17126 / 17325 | `equation62_restrict`, `Definition15Geometry.lemma6_1` | (6.2)가 restriction에 대해 안정적(직접 계산) | U(쉬움) |
| 11 | 17818 | `proposition16_strictEqualityTwistedOneForm_isSheaf` | (6.2)를 만족하는 매끄러운 𝔤값 1-form이 (custom) sheaf를 이룸. hypothesis 없음 | U |
| 12 | 6844 / 8317 / 8775 | `TruncatedGaugeCovariantDGA.curvature_gaugeTransform`, `PaperFaithfulConnection.Core.nablaSquared_eq_curvatureAction`, `LocalFrameChange.curvature_transformConnection` | `F(A^g)=g⁻¹F(A)g`, `∇²=F·` | C(class 법칙) / U(장난감 DGA 위) |
| 13 | 20090 | `Definition18Proposition19ActualSpecialization.proposition19_actual_without_H3` | H1, H2, 최소자, **최소자의 flatness를 가정하면** `M=R=0` | C/T(산술) |
| 14 | 20771 | `Proposition20ActualQGaugeSpecialization.globalRestrictionForkIsLimit` | 전역 q-gauge 단면이 (6.13)의 Type-equalizer 극한 | U |
| 15 | 14659 / 14436 | `Definition14Boundary.MathlibBridge.mathlibSubtypeEqualizerIso`, `toMathlibPresheaf_isSheaf` | custom `IsSheafLike` ⇒ Mathlib `IsSheaf`. subtype equalizer ≅ Mathlib `equalizer` | U(진짜 bridge) |
| 16 | 15858 | `Proposition15FunctorBridge.F_torCompatibility` | `:= AddEquiv.refl _` | T |
| 17 | 23270 | `Proposition15ActualFunctor.constantTorComparisonIso_model` | 상수 functor 사이의 NatIso. 성분은 #4 | U이지만 내용상 상수 |
| 18 | 10708 | `Mmock.certificate` | CertifiedGerm 필드의 재포장 | A |

## 3. 탈출구와 신뢰 기반

- 주석과 문자열을 제거한 사본에서 `sorry`/`admit`/`axiom`/`native_decide`/`opaque`/`unsafe`/`implemented_by`는 0개다(lead가 확인한 사실, 재확인 안 함).
- **컴파일**: lead가 로컬에서 빌드했다. exit 0, 0 errors, 341 warnings, sorry 경고 없음. 따라서 헤더(9줄)와 `PaperMap`의 "build deferred" 문구는 **이미 낡은 표기**다.
- `set_option maxHeartbeats 800000`은 1곳뿐이다(8306줄, `potential_action_assoc`, `simp … <;> ring`).
- custom `elab`/`macro`/`syntax`/`notation`은 없다.
- `#print axioms`는 1,989줄이다(24,613줄–끝). 감사용으로 유용하다. 다만 이 정리들이 실제로 무엇을 증명하는지는 별개 문제다.
- `decide`는 작은 항에만 3회 쓰였다. `Gamma_mem`의 `ZMod 2` 등식(9541), `paperTrace_items_nodup`(24501), CRT example(21592)이다. 위험하지 않다.
- `Classical.choose`는 8회다. 모두 gluing 증인이나 cover index를 고르는 데 쓰였다(5870, 9656, 14866, 17454 등). 데이터 조작은 없다.
- **주의할 smell**: 16,138줄의 `local instance (priority := 100000) canonicalNormedSpaceComplex : NormedSpace ℂ ℂ`. 우선순위를 강제로 덮어써 instance diamond를 피하는 해킹이다. 컴파일이 되므로 defeq는 성립하는 것으로 보이지만, 깨지기 쉽다.
- `Inhabited False`류의 속임수나 `default` placeholder는 발견하지 못했다.

## 4. 조건부 인증 감사 (핵심)

### (a) CIRCULAR — 가정이 곧 결론이거나 결론을 자명하게 함축
- `lemma6_1_covariance_restrict` (5335) `:= hCov.restrict_stable hUV hA`. 추상 Lemma 6.1은 가정 `IsRestrictionStableCovariance` 그 자체다. 같은 패턴이 `lemma6_1_qGauge_certificate` (13628, `hMC hUV hA`)와 `MathlibFreeFallback.RestrictionStableCovariance` (21322)에도 있다. **다만 기하적 버전 `Definition15Geometry.lemma6_1` (17325)은 `equation62_restrict`로 실제로 증명했다(=(d)).**
- `TruncatedGaugeCovariantDGA.legacyConnectionAdmissibleGaugeAssumption` (6412, class 필드). `gaugeTransform_admissible` (6597)은 이 필드의 투영일 뿐이다. 파일 스스로 "legacy assumption"이라고 명시한다(7018–7039).
- `QGaugePresheaf.EffectiveMassFunctional` (13923): `mass_vanishes_on_flat`, `potential_vanishes_on_flat` 필드가 결론과 같다. "legacy"로 표시되어 있다. 같은 곳의 `FlatSector`(13916)는 `QCurvature x = x`로 정의되어 있어, 이름과 달리 영곡률이 아니다.
- `QGaugeSPTBridge.obstruction_law` (15948) → `bridge_obstruction_eq_gcd` (15957) `:= B.obstruction_law U x`.
- `QGaugePresheaf.QCovariantDerivative` (13312): `local_formula`, `restrict_Dq`가 필드다. 정리 13324, 13329는 accessor다.
- `Mmock.PaperAnalyticInput` (10585): Prop 13과 Thm 5.1의 결론 필드(`proposition13_transport`, `theorem51_realAnalytic` 등)가 판정 대상으로 삼는 술어(`CuspTransport`, `SpectrallyControlledAtCusp`, `RealAnalyticCompletion`, `SpectrallyControlledCompletion`)를 **같은 structure의 필드로 함께 받는다.** 술어를 `fun _ => True`로 두면 그만이므로 내용이 없다(content-free).
- **준순환**: `Definition15Geometry.GaugeAdmissible` (18475) `:= Central ∧ RhoCompatible ∧ Equation62 (D.maurerCartan U g)`. g⁻¹dg가 (6.2)를 만족한다는 조건이 정의 안에 들어 있다. 그래서 "(6.2) 보존" 정리 `equation62_gaugeAction` (18589)은 `equation62_add` 한 줄로 끝난다. 게다가 **central gauge로 제한**하므로 비가환 내용(`g⁻¹Ag`)이 정의상 `A`로 사라진다(`centralConjugate := A`, 18537).
- `Definition18…checklist_7_P1_unconditional`의 필드 `general_minimizer_is_retained_as_input` (20212)는 `hmin → hmin` 형태의 동어반복이다.

### (b) SUBSTANTIVE — 그럴듯한 깊은 입력이고, 증명하는 것과 분명히 분리되어 있음
- `Definition11.AnalyticData` (9788): Hilbert 공간, 조밀한 정의역, 선형 연산자 두 개. 아무 선형사상이나 허용하므로 실제 PDE 내용은 없다. 입력 경계로서는 정직하다.
- `Proposition14.HqEvolutionData` / `HqEvolutionWellPosed` / `AnalyticInput` (14832, 14843, 15310): 정직한 경계다. 파일 스스로 `evolutionInterface_audit` (22371)로 **생성자 `Hq`와 `SolvesHq` 사이에 연결이 없음**을 증명해 보였다.
- `HalfWeightBranch` / `MultiplierSystem` (16210, 16254): η 구성으로 **해소됨((d))**.
- `Definition12Tensor.LocalTrivializationComparison` (11618), `PairTensorEquivalenceData` (11872): 동형 데이터를 요구하는 정직한 가정이다.
- `CurvatureInnerProduct` (19692), 측도 `μ`, `HypothesisH1/H2/H3` (19889–19956), `IsGlobalMinimizer`: Prop 19의 입력이다. 다만 `Astar_is_flat`/`hflat`(최소자가 flat이라는 것)까지 가정한다. 논문이 이를 결론으로 주장하는지는 확인하지 못했다. 그렇다면 결론의 핵심 일부를 가정한 셈이다.
- `MaurerCartanCalculus` (18448): mfderiv의 곱·역원·restriction 법칙을 필드로 둔다. ℂˣ에 대한 실제 인스턴스는 **구성되지 않았다**.
- `IsSheafLike F`, `IsLocalCovariance` (Prop 16과 20의 추상 버전): 구체 모델에서 모두 해소됨((d)).
- `TensorToModularQGaugeBridge` (23593), `QGaugeDGARealization` (23708): 논문이 정의하지 않은 층간 화살표를 데이터로 노출한다. 유일한 인스턴스는 `zeroModel`이고, `zeroModel_not_nontrivial`로 자명함까지 증명해 두었다. 매우 정직한 처리다.

### (c) SUSPECT-VACUOUS — 실제 대상에 대해서는 사실상 공허할 수 있음
- **`Mmock.CertifiedGerm` + `CommonAnnulus` (10093, 10211)**: annulus가 `inner < 1 < outer`를 요구하고, 그 위에서 inside 급수 `f`, `psi`, `S`가 모두 수렴해야 한다. 진짜 mock theta 함수는 \|q\|=1을 자연경계로 가지므로 \|q\|>1에서 수렴하지 않는다. 따라서 **논문의 실제 대상은 이 타입에 들어갈 수 없다.** 실제 인스턴스도 상수 급수(`unitCertifiedGerm`, 21927)와 단항식 q(`degreeOneCertifiedGerm`, 21969)뿐이다. 파일은 "ℍ에서 \|q\|>1인 매개변수는 없다"는 반증까지 했으면서, annulus 정의의 이 결함은 짚지 않았다.
- 같은 이유로 `Definition14Boundary`(GloballyCompatible: \|q\|>1 지점에서 `f(q)=G(q⁻¹)`)와 그 equalizer sheaf도 유한급수 모형에서만 내용을 가진다.

### (d) DISCHARGED — 파일 안에서 실제로 증명됨
- Prop 16 구체판: `proposition16_strictEqualityTwistedOneForm_isSheaf` (17818). sheaf 성질 `strictSmoothOneFormIsSheaf` (17691)와 locality `equation62IsLocalCovariance` (17734)를 직접 구성했다.
- Lemma 6.1 기하판: `lemma6_1` (17325) ← `equation62_restrict` (17126).
- branch와 multiplier의 존재: `EtaHalfWeight.branch_multiplier_exists` (16637).
- Prop 20의 `hAq`: `proposition16_supplies_hAq` (20307).
- Tor'₁ ≅ 순환 kernel: §E.1–E.3 전체(4536–5295).

### 참조·예시 인스턴스 (degenerate인가, 실제 대상을 담는가)
- **실제 대상을 담음**: `EtaHalfWeight.multiplier`(η 기반, 실제 Γ(2) 작용), `Tor1ZDerivedComparison.standardProjectiveResolution`(실제 사영 분해), `Bundle.Trivial X (Fin 2→ℂ)`(Mathlib의 진짜 벡터다발).
- **degenerate**:
  - `Mmock.zeroKernel`/`zeroCertifiedGerm` (10289, 10300)과 `unitKernel` (상수 1).
  - `Definition11.scalarAnalyticData` (21672): Laplacian = 0, potential = 0. `twoComponentAnalyticData`는 좌표 사영이다.
  - `Proposition14.correctedEvolution`(생성자 0), `nablaQ`(연결 0), `canonicalFlatTransport`(항등).
  - `Definition13QCovariant.logDifferential := 0` (12129), `zeroFibreOperators`, `identityFibreOperators`. "진짜 q·d/dq"는 단항식 `c·q`에서 `q·d(cq)/dq = cq`라는 사실뿐이다(22227).
  - `UnconditionalSection63Witness.GaugeGroup := Multiplicative (Fin 0 → ℂ)` (18781). **자명군**이고 ρ=1이다. checklist 6.3의 "non-vacuity" 증인이다.
  - `AdaptedGeometryCover.canonical` (20363): inside, outside, cusp가 모두 `⊤`.
  - `checklist_6_1/6_2_unconditional`은 `PUnit`과 ⊥ 위상 위의 `Core.zero`.
  - `Proposition15ActualFunctor.localSpectralProfile := (s, 0)` (23009). `actualSource`는 항등사상 두 개의 equalizer다(23347).
  - `PaperElementaryIntegration.tensorToActualQGauge_zeroModel` (23557)은 모든 것을 0으로 보낸다.
  - `canonicalVacuum`, `zeroH1/H2/H3`(영 함수열).
- 대부분 이름이나 주석으로 "zero model"임을 밝힌다. 그러나 헤더(129–152, 221–227줄)는 "FORMALIZED with nonzero fibres … genuine q·d/dq … empty-context closure"라고 적어, 증인이 장난감이라는 사실을 독자가 알아차리기 어렵다.

## 5. 정의 충실도

| 대상 | 정의 방식 | 판정 |
|---|---|---|
| Tor₁ | `Tor1Model := ZMod (gcd)` (2974) 프록시와 별도로 **`MathlibTor1Z := (Tor' (ModuleCat ℤ) 1).obj (ZMod M) .obj (ZMod N)`** (5032). `isoLeftDerivedObj`를 통한 bridge `mathlibTor1ZIsoCyclicModel` (5057), `mathlibTor1ZEquivZModGcd` (5088) | **충실하고 bridge도 있음**. 다만 첫 변수 derived인 `Tor'`이며, `Tor ≅ Tor'`는 Mathlib에 없다고 스스로 밝힘(5290). M≠0, N≠0 조건 필요. `card_Tor_eq_exp_IC` (1114)는 이름과 달리 `gcd = exp(IC)`만 말함 |
| Ideal intersection / exact sequence | Mathlib `Ideal`, `AddSubgroup`, `ShortComplex Ab`, `QuotientAddGroup` | 충실 |
| `Γ(2)\ℍ`, q-parameter, deck 작용, `(cτ+d)` | Mathlib `CongruenceSubgroup.Gamma 2`, `MulAction.orbitRel`, `UpperHalfPlane.denom`, `deriv_smul` | 충실 |
| weight-½ multiplier | `ModularForm.eta`와 판별식의 slash 불변성으로 실제 구성 | 충실(우수) |
| 매끄러운 𝔤값 1-form, (6.2), deck pullback | `ContMDiff`, `GroupLieAlgebra`, `mfderiv` | 충실. sheaf는 custom API이며 Mathlib bridge가 있음 |
| Sheaf / equalizer | custom `PresheafLike`/`IsSheafLike`(5306, 5834)와 `QGaugePresheaf`, `MockBundle`, `QLocalSystem`, `LinearPresheaf`(사실상 같은 구조 5벌) | **bridge 있음**: `toMathlibPresheaf_isSheaf` (14436, 20810 — 중복), `mathlibSubtypeForkIsLimit` (14641). 단방향(custom⇒Mathlib) |
| Definition 11 q-local system | 고정 kernel의 locally constant sheaf, `transport := LinearEquiv.refl` | "corrected"라는 이름의 **자명화**. 논문의 radius 의존성이 사라짐 |
| Mmock sheaf | `LocallyConstant U (CertifiedGerm K)` | 상수 sheaf. 실제 mock theta는 들어갈 수 없음(§4(c)) |
| Definition 12 tensor | Mathlib `TensorProduct`, `TensorProduct.map` | 대수적으로는 충실. 재료(Lq, Mmock)가 자명화되어 있음 |
| Definition 13 Dq | `T⊗id + id⊗S`를 상수 frame `dlog r`과 tensor. `logDifferential := 0` | 형식만 있음. radial 미분은 0 |
| Definition 16/17, DGA | y-불변 다항식 차트 `ChartForm n` over `Polynomial ℂ`, `Omega X n U := Matrix 2×2` (**U와 무관**), `restrictHom := id` | 대수 법칙(graded Leibniz, d²=0)은 진짜. 기하적으로는 X와 무관한 장난감 |
| Prop 17/18 최종 연결 | `Connection U := (modular (6.2) 단면) × (locally constant 다항 행렬 form)` (19267) | **서로 무관한 두 성분의 곱**. 곡률과 gauge 변환은 두 번째 성분에만 작용하고 q-gauge 장에는 닿지 않음. 이 사실은 `QGaugeDGARealization`으로 스스로 인정 |
| Prop 15 functor | (구판) 데이터를 복사, (신판) balanced equalizer와 `(s,0)` 프로파일 | 사실상 동어반복 |
| Curvature energy (6.12) | Mathlib Bochner `∫ x, ⟪F,F⟫ ∂μ` | 형식 충실. 내적과 측도는 입력 |

## 6. 실질 수학 내용

진짜로 비자명한 증명(Mathlib을 실질적으로 활용한 것):
1. §E.1–E.3 (4536–5295): ZMod M의 2항 자유 사영 분해, `QuasiIso`, tensor 후 degree-1 homology의 kernel 계산, `ProjectiveResolution.isoLeftDerivedObj`로 Mathlib `Tor'`와 비교. **가장 가치 있는 부분**이다.
2. `Tor1Canonical.gcdToKernelEquiv` (3356), `Tor1PrimePowerCanonical.powerShiftEquiv` (3747)와 양쪽 naturality 및 유일성(3974–4104). 생성원을 고르지 않는 정준 동형이다.
3. `EtaHalfWeight` (16327–16685): η^24의 slash 법칙, 12차 단위근 잔차, 연결성으로 잔차가 상수임을 보임, √로 ν를 구성.
4. `strictSmoothOneFormGlue` (17566–17615): `liftPropAt_iff_comp_inclusion`으로 매끄러움을 붙임.
5. 비가환 gauge-covariance 계산: `curvature_gaugeTransform` (6844), `nablaSquared_eq_curvatureAction` (8317), `curvature_transformConnection` (8775).
6. 반증 4개: 9595, 21646, 21628, 22443.
7. custom sheaf에서 Mathlib sheaf로 가는 bridge (14436)와 equalizer 극한 (14641, 20771).
8. 초등 정수론: `crt_solvable_iff` (724), `card_ker_mulLeft` (1070), `gcd_eq_prod_primeFactors` (1095).

줄 수 기준 대략적 구성(추정, ±5%):
- **진짜 비자명 수학: ~22%** (§E 약 3,000줄 중 절반, η·Def15 기하 약 1,500줄, DGA 계산 약 900줄, bridge와 반증 약 600줄).
- **정당하지만 일상적인 API**(restriction 법칙, simp 보조정리, presheaf 법칙, 덧셈군 instance 등): ~30%.
- **스캐폴딩: ~48%**. 내역은 Certificate structure와 증명 약 3,900줄, `#print axioms` 약 2,000줄, 헤더·원장·서술 docstring 약 2,500줄, `PaperMap` 문자열 원장 약 380줄, 중복 API(PresheafLike/QGaugePresheaf/MockBundle/QLocalSystem/LinearPresheaf, `CurvatureAlgebra`와 `AbstractCurvatureOperations`, 두 Mathlib bridge, `MathlibFreeFallback` 전체, 소수 거듭제곱 특수화의 `simpa [Pk]` 복제본) 약 2,500줄, zero model 약 600줄.
- 논문의 해석적 핵심(mock theta, Kloosterman, Kuznetsov, scattering, mass gap)은 **0%**다. Advanced 파일로 위임했다고 적혀 있다.

## 7. 수학적 정확성 (과장·오표기·약화)

- 헤더 129–136줄: "`Mmock` actual q-series sheaf … FORMALIZED". **실제 mock theta 급수는 `CertifiedGerm`에 들어갈 수 없다**(annulus가 \|q\|=1을 가로지름). "actual"은 과장이다.
- 헤더 283–296줄과 Definition 16/17: "genuine trivial complex vector bundle … ∇ = d + A". 그러나 단면은 X와 무관한 다항식 좌표이고 restriction은 항등이다. `toGeometricSection`은 임의의 `coordinate : X → ℂ`에 의존한다.
- 헤더 310–326줄: "Proposition 17/18 final specialization … derived gauge covariance". 곡률과 gauge 변환은 다항 DGA 성분에만 적용된다. (6.2) q-gauge 장과는 연결이 없고(`frameGaugeTransform`이 `A.1`을 그대로 둠, 19465), 그 연결은 `QGaugeDGARealization.zeroModel`만 존재한다.
- 헤더 297–309줄: checklist 6.3 "concrete non-vacuity witness". 이 증인은 **자명군** `Multiplicative (Fin 0 → ℂ)`이다. ℂˣ에 대한 `MaurerCartanCalculus`는 구성되지 않았다. admissible gauge는 central(가환)로 제한된다.
- Prop 19 (`proposition19_actual_without_H3`, 20090): 최소자의 flatness `hflat`을 가정한다. 결론은 "음이 아닌 두 항의 합이 0이면 각각 0"이라는 산술이다. 헤더 327–346줄의 "FORMALIZED with the actual A_q(X) global connection" 문구에 비해 내용이 매우 얇다.
- Prop 15 (`F_torCompatibility := AddEquiv.refl`, 15858; `constantTorComparisonIso_model`, 23270): Tor 호환성은 상수 functor 사이의 것이라 sheaf에 의존하지 않는다. 주석에서 "fixed-parameter model"이라고 인정한다.
- `card_Tor_eq_exp_IC` (1114): 이름은 Tor를 말하지만 Tor는 등장하지 않는다(gcd 등식).
- Definition 11 "corrected": fibre가 r에 의존하지 않고 transport가 항등이다. 논문의 local system을 상수로 바꾼 것이며, 수정이라기보다 대체다.
- 긍정적인 점: 논문의 결함 세 가지(Def 11의 π 비정합, Prop 13의 cusp 수송 불가, Prop 14 유일성 실패)를 **정리로 반증**했다. 이 반증은 수학적으로 옳다. Γ(2)의 원소는 좌상단 성분이 홀수이므로 ∞↦a/c≠0이다. Γ(2)의 cusp ∞, 0, 1이 서로 비동치라는 표준 사실과 일치한다.

## 8. 코드 품질

- 파일 하나가 26.6k줄이다. 최소 7–8개 모듈로 나눠야 한다(Prop21/Tor, sheaf API, DGA, Def11–14, Def15 기하, Prop17–20, 감사·원장).
- 같은 presheaf 구조가 5벌, Mathlib bridge가 2벌(14388과 20785), curvature 인터페이스가 3벌(`CurvatureAlgebra`, `TruncatedGaugeCovariantDGA`, `AbstractCurvatureOperations`) 있다. `simpa [Pk]` 소수 거듭제곱 복제본이 수십 개다.
- Certificate structure 64개: 이미 증명한 보조정리를 필드에 다시 담는 패턴이다. 검색성은 좋지만 정보는 늘지 않는다. `#print axioms` 약 2,000줄은 빌드 로그용으로는 좋지만 소스 파일 안에 있을 이유가 없다.
- 이름 문제: `FlatSector`가 두 곳에서 다른 의미로 쓰인다(13916은 고정점, 9076은 영곡률). `Eq`라는 이름의 def(13414)는 `Eq`와 혼동될 수 있다. `Definition16.Eq`도 같다.
- 낡은 표기: "(build deferred)" 수십 곳, `BuildStatus.deferredToUser`. 실제 빌드는 이미 성공했으므로 갱신이 필요하다.
- 견고성: heartbeat 상향은 1곳뿐이라 양호하다. `simp … <;> ring`/`abel` 연쇄가 많아 Mathlib 버전에 취약할 수 있다. 16138줄의 instance 우선순위 해킹이 있다.
- Mathlib 상향 후보:
  - (i) `Tor' (ZMod M) (ZMod N) ≅ ZMod (gcd M N)` 및 정준 `gcdToKernelEquiv`.
  - (ii) η에서 weight-½ multiplier 구성(`etaResidual_eq_base` 등).
  - (iii) `ZMod`에서 `ker (mulLeft M)`의 크기(`card_ker_mulLeft`).
  - (iv) 초등 CRT `crt_solvable_iff`(Mathlib에 유사 정리 있음, 확인 필요).

## 9. 컴파일 위험

- **lead 검증**: 고정된 toolchain에서 Mock2는 exit 0, 0 errors, 341 warnings, sorry 경고 없음. 브리프에 언급된 예전 로그(0 errors / 386 warnings)와도 일관된다.
- 남은 위험은 깨지기 쉬운 `simp` 연쇄와 instance 우선순위 해킹이다. 현재 커밋에서 실제로 실패하는 지점은 없다.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | **9** | 0 errors(lead 검증), sorry·axiom 없음, heartbeat 상향 1곳. instance 우선순위 해킹이 유일한 흠 |
| 조건부 인증의 정직성(비순환성) | **6** | `_zeroModel` 명명, 반증, PaperMap의 `paperAssumption` 표기 등 자기감사가 이례적으로 정직하다. 그러나 추상 Lemma 6.1=가정, legacy 가정 필드, content-free인 `PaperAnalyticInput`, `GaugeAdmissible`의 준순환, Prop 19의 flatness 가정이 있고, "unconditional" 헤드라인이 자명군·영 연산자·상수 급수 증인에 기대며, 헤더가 과장되어 있다 |
| 수학적 실질성 | **5** | Mathlib Tor' bridge, η multiplier, 매끄러운 sheaf, 반증은 진짜다. 논문의 해석적 핵심은 0이고 대부분의 "실제 대상"이 장난감 모형이다 |
| 정의 충실도 | **5** | Tor, Γ(2)\ℍ, η, (6.2)는 충실하다(8–9점). Mmock(실제 대상 배제), Lq(상수), DGA(U 무관), Prop 17/18 연결(무관한 곱), Def 13(미분 0)은 자명화되었다(2–3점) |
| 코드 품질·유지보수성 | **4** | 단일 26.6k줄, 중복 API 5벌, Certificate 64개, `#print axioms` 2,000줄, 낡은 "deferred" 표기. 개별 증명은 깔끔하고 상향할 만한 보조정리가 있다 |
| **종합** | **5.5** | 정직하고 컴파일되는, 수학적으로는 얇은 "구조 형식화"다. Prop 21(Tor)과 Def 15(η, (6.2), sheaf)는 높이 평가할 만하고, 나머지는 장난감 모형 위의 스캐폴딩이 대부분이다 |

---

## 커버리지 기록
모든 범위를 Read로 직접 읽었다(약 1,000–1,100줄 단위).
1–1000, 1001–2000, 2001–3000, 3001–4000, 4001–5000, 5001–6000, 6001–7000, 7001–8000, 8001–9000, 9001–10000, 10001–11000, 11001–12000, 12001–13000, 13001–14000, 14001–15000, 15001–16000, 16001–17000, 17001–18000, 18001–19000, 19001–20100, 20101–21200, 21201–22300, 22301–23400, 23401–24500, 24501–25400.
25401–26607은 `grep -v '^#print axioms '`로 확인했다. 주석 2줄과 `end AxiomAudit`, `end Mock2` 외에는 모두 `#print axioms`다(24,613–26,603에 총 1,989줄). 이 구간은 **목록을 훑어봄(skim)**.
보조 자료: `scan/decls_cls.json`(file=`Mock2`)으로 통계를 집계했고, `scan/Mock2.code.lean`으로 heartbeat·`decide`·`Classical.choose` 개수를 셌다.
