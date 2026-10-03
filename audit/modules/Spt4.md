# Spt4 모듈 감사 보고서

대상: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Spt4.lean` (8,714줄, `namespace Spt4`)
선언 통계(decls_cls.json): 983개. theorem 610, def 232, abbrev 31, structure 43, inductive 27, example 26, instance 13, class 1. accessor 판정 20개, 본문이 `rfl`·`Iff.rfl`·`decide`·`cases <;> rfl`뿐인 theorem 85개.
**inductive 27개는 모두 상태/라벨 열거형**(`ClaimStatus`, `NeronPiece`, `Delta52Boundary` 등)이고, `Bool` 상태표 def가 12개 있음.
읽기 범위: 1–8714 전 구간을 순서대로 읽음(아래 커버리지 로그 참고). lake/lean은 실행하지 않음.

---

## 1. 목적과 논문 대응

- 헤더(1–27)에 따르면 이 파일은 논문 #4 "Primality Sheaves and the Étale–Motivic–Derived Package on Arithmetic Curves"의 단일 파일 형식화입니다.
  - PART I(§A–§P): "모든 정의·보조정리·명제·정리·따름정리를 REAL proof로" 형식화한다고 주장합니다.
  - PART II(§Q–§W): sound/complete 인증서 계층입니다.
  - PART III 이후(§Δ1–§Δ58): 체크리스트 확장과 "boundary" 절들이 이어집니다.
  - 헤더는 "증명되지 않은 것은 Conj 8.3.7 하나뿐"이라고 주장합니다.
- 대응하는 논문 번호(`claimIndex`, 5956–6015, 59개 항목):
  - Prop 2.1, Rem 2.2, Lem 2.3, Def 2.4, Prop 2.5, Lem 2.6, Ex 2.7/2.8
  - Thm 3.9, Rem 3.10/3.11, Def 3.12, Lem 3.13, Prop 3.14, Thm 3.15, Ex 3.16, Thm 3.17, Def 3.18, Prop 3.19–3.21, Lem 3.22, Thm 3.23/3.24, Ex 3.25, Prop 3.26, Lem 3.27, Rem 3.28
  - Prop 6.29/6.30, Rem 6.31, Lem 6.32, Prop 6.33, Rem 6.34, Thm 6.35/6.36, Rem 6.37, Ex 6.38
  - Thm 7.1, Cor 7.2, Prop 7.3, Cor 7.4, Lem 7.5, Prop 7.6, Lem 7.7, Prop 7.8, Cor 7.9, Rem 7.10
  - Def 8.2.1, Thm 8.2.2, Rem 8.2.3, Prop 8.2.4, Lem 8.3.1, Prop 8.3.2, Cor 8.3.3, Lem 8.3.4, Prop 8.3.5, Thm 8.3.6, Conj 8.3.7
- 파일은 논문 Remark 3.10의 "εp = min" 주장이 틀렸다고 스스로 정정하고 있으며(22–25), `factorization_gcd_apply`/`factorization_lcm_apply`로 이를 뒷받침합니다. 이 정정 자체는 올바릅니다.

## 2. 헤드라인 정리

상태 표기: U = 무조건부, C = 조건부, A = 접근자(필드 꺼내기), T = 자명/동어반복.

| # | 선언 (줄) | 진술(요약) | 상태 |
|---|---|---|---|
| 1 | `arithCechδ0_range_eq_zmultiples_gcd` (401), `arithCechH1_iso_ZMod_gcd_int` (428) | `range((a,b)↦Ma−Nb) = gcd·ℤ`, `coker ≃+ ZMod (gcd M N)` | U (Bézout, 실질적이나 초급) |
| 2 | `crt_solvable_iff` (444), `finiteCover_certify` (1359) = `cor_7_9` (4119) | CRT 해 존재 ⟺ `gcd ∣ a−b`. 쌍별 서로소 유한 덮개에서 해 존재와 lcm 법 유일성 | U |
| 3 | `TorH1_iso_zmod_gcd` (1389), `TorH1_directSum` (2819), `ExtH1_iso_zmod_gcd` (7984) | `ker(×M on ℤ/N) ≃+ ℤ/gcd`, 소수별 ⊕ 분해, `coker(×M) ≃+ ℤ/gcd` | U. 단 프록시 객체(5절 참고) |
| 4 | `Deep.piN_quasiIso` (4954), `Deep.projResolution` (4998), `torLeftDerived_iso_resolutionHomology` (5034) | `0→ℤ→ℤ→ℤ/N`이 Mathlib의 진짜 `ProjectiveResolution`이고, Mathlib `leftDerived(tensorLeft ℤ/M)`₁ ≅ resolution H₁ | U (진짜 범주론) |
| 5 | `Deep.LeftDerivedComputesResolutionH1` (5057), `leftDerivedComputesResolutionH1_iff_kernel` (6824) | 범주론적 Tor₁ ≅ ℤ/gcd라는 주장. 동치 명제로 환원만 되었고 **증명되지 않음** | open (Prop로만 기록) |
| 6 | `truncatedLog_sub_leading` (1647), `thm_8_2_2` (4192) | `p^k ∣ u`, p 홀수 ⇒ 절단 log − u의 valuation ≥ 2k (합 ≠ 0 가정 포함) | U |
| 7 | `PadicLogP.plog_summable` (5282), `plog_norm_le` (5353), `plog_sub_self_inP2kZp` (5484), `ab_sync_quadratic` (5538) | ℚ_[p]에서 수렴하는 log(1+u). ‖log(1+u)‖ ≤ ‖u‖, `log(1+u)−u ∈ p^{2k}ℤ_p` (p 홀수) | U (파일에서 가장 좋은 해석적 내용) |
| 8 | `GeometricDetectors.master_identity` (1842), `thm_7_1` (4017) | étale bump = motivic jump = b₁+Σδ | **A/C 순환** |
| 9 | `all_detectors_agree` (1036), `prop_3_26` (3743) | 5개 검출기 TFAE / 좋은 소수에서 소멸 | **C 순환** |
| 10 | `twoOpen_cech_eq_derived_all_degrees` (974), `PrincipalCoverAcyclic.computes` (5197) | Čech ≃ derived (모든 차수) | C. 내용 대부분이 가설에 들어 있음 |
| 11 | `thm836` (2293), `thm_8_3_6_external` (4369) | AP 소수 밀도 = 1/φ(q) | **C 패스스루** (`:= h a q hcop`) |
| 12 | `master_equivalence` (8336) | étale bump = motivic Euler jump = comb, "무조건부, 진짜 객체 사이" | **C 순환** (`E.bump_eq` 필드와 `hmot` 가설) |
| 13 | `hasse_iff_frobenius_eigenvalue` (8446), `hasse_iff_degree_nonneg` (8453) | aₚ² ≤ 4p ⟺ α+ᾱ=aₚ, αᾱ=p인 α 존재 ⟺ 이차식 PSD | U이지만 대수적 재진술. 실제 곡선과 연결 없음 |
| 14 | `goodReduction_singularSet_empty` (5616), `fec_gate_iff_reduction_isElliptic` (7676) | p ∤ Δ ⇒ mod p 곡선의 특이점 집합 = ∅, `ecGate W p ↔ (W mod p).IsElliptic` | U (Mathlib 얇은 래퍼) |
| 15 | `conj_8_3_7_evidence` (4388) | support가 유한하면 `SublinearCohDensity` | U, 자명 |

## 3. 탈출구와 신뢰 기반

- 주석과 문자열을 제거한 사본 기준으로 `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`는 모두 0입니다. 커스텀 `elab`/`macro`/`syntax`도 없습니다.
- `set_option maxHeartbeats 800000 in`이 한 곳 있습니다(4945, `resC_d_succ_zero`). 이는 `ChainComplex.of` 차분의 `rfl` 증명이며, 정의 펼침 비용이 큰 것으로 보입니다.
- `open Classical in`이 한 곳 있습니다(6192, `actualDerivedDetector`의 `if Subsingleton …`). 무해합니다.
- `default`는 `Unique`/`Subsingleton` 위에서만 쓰입니다(930, 985). 데이터를 조작하는 `Inhabited` 트릭은 없습니다.
- `decide`는 모두 작은 항에만 쓰입니다: gcd 소규모 sweep(2337–2340), 59개 String 목록의 `Nodup`/`filter`(6021–6053), Bool 상태표. 위험 수준이 아닙니다.
- **`#print axioms`나 axiom-firewall 명령이 전혀 없습니다.**
  - 마지막 "Axiom audit" 절(8690–8712)은 주석만 있는 빈 section입니다.
  - 그런데도 헤더와 §Δ7(2879–2880)은 "`#print axioms` over the whole file confirms…"라고 주장합니다. 근거가 파일 안에 없습니다.
- 7660 주석은 "현재 Mathlib(v4.30-rc1)에서 `#check`로 재확인"한다고 하지만 `#check`는 없고, 실제 툴체인도 v4.33.0-rc1입니다. 낡은 주석입니다.

## 4. 조건부 인증 감사 (핵심)

분류 표기: (a) 순환, (b) 실질적 가설, (c) 공허 의심 또는 거짓, (d) 파일 안에서 해소됨.

| 가설 / 인터페이스 (줄) | 사용처 | 분류 | 근거 |
|---|---|---|---|
| `DetectorBridge` (1022) | `all_detectors_agree`, `prop_3_26` | **(a)** | 필드 `etale_gate : etale = 0 ↔ gcd = 1` 등이 결론 자체입니다. 4개 값은 임의의 ℕ이고 étale 이론과 연결이 없습니다. 예시 `arithDetectorBridge`(1048)는 네 값 모두 `detector`로 퇴화되어 있습니다. |
| `CurveData.normalization` (1067) | `cd_master_identity` (1076) | **(a)** | 필드 `h1X = h1U + (b1+δ)`가 곧 결론입니다. `CurveData.ofSES`(1799)는 SES와 `hdefect`에서 이 필드를 도출하므로 부분적으로 (d)입니다. 다만 `hdefect`가 기하학적 내용 전부를 담고 있습니다. |
| `GeometricDetectors` (1828) | `master_identity`, `detectors_tfae`, `thm_7_1`, `cor_7_2`, `prop_7_3`, `prop_7_8`, `good_prime_geometry`, `listing2_cert` | **(a)** | `etale_eq : etaleBump p = comb p`, `motivic_eq`가 결론입니다. 예시 `arithGeometricDetectors`(2520)는 모두 0입니다. |
| `MasterIdentityCert` (2406) | `.sound`, `master_full` | **(a)** | 위 구조체에 `hcomb`를 추가한 것입니다. `arithMasterIdentityCert`(4037)는 0과 자명 fibre입니다. |
| `DetectorAgreement` (1979) | `detectors_certified` | **(a)** | `etale = detector`를 가정하고 `etale = 0 ↔ gcd=1`을 결론합니다. |
| `CechComputesDerivedLowDegree` + `highVanish` (965, 977) | `twoOpen_cech_eq_derived_all_degrees` | (b)이나 사실상 (a) | `derivedH`는 임의의 타입족이고 Mathlib의 sheaf/derived cohomology와 연결이 없습니다. 만족 예시는 `derivedH := Čech` 자기 자신(2531, 5207)뿐입니다. |
| `PrincipalCoverAcyclic` (5181) | `.computes` | **(a)** | "Cartan acyclicity"라는 이름과 달리 affine이나 sheaf 조건은 없고, 위 두 결론을 필드로 묶은 것입니다. |
| `DirichletDensityAP` (2274) | `thm836_part2` (2280) `:= h a q hcop`, `thm836`, `apDensity_general_via_external` | (b) 가설 자체는 참이나, 사용은 (a) 패스스루 | 디리클레 정리의 밀도형(π 분모)은 참입니다(q=0,1 경계도 일관됨). 정리는 가설을 그대로 반환할 뿐입니다. §Δ57(8505–8578)은 "외부 입력을 genuine 정리로 교체"한다고 쓰지만, 인용된 것은 L-급수 하한(`LSeries_residueClass_lower_bound`)일 뿐이고 `DirichletDensityAP`는 여전히 증명되지 않았습니다. |
| **`HasseTheorem` (2754)** | 사용처 없음(정의만) | **(c) 거짓** | `∀ p cardEp, (p+1−cardEp)² ≤ 4p`입니다. 곡선 인자 `_E`를 쓰지 않고 모든 `cardEp`에 대해 정량하므로 모든 E에 대해 **거짓**입니다(예: p=0, cardEp=5에서 16 ≤ 0). docstring은 "genuine trace가 Hasse bound를 만족"이라고 설명합니다. `hasse_supersingular_satisfiable`(2759)이 "non-vacuous"를 주장하지만 실제로는 `HasseBound 0 p`만 증명합니다. |
| `GoodReductionData` (2773) | `gate_faithful` (5650) | (a), 퇴화 | `ofGate`(2783)에서 `minimal := True`, `good := gate`입니다. |
| `AbstractCurveFibre` (6431) | `etale_eq_comb`, `motivic_eq_etale`, `master_identity` | `motivic_eq_etale`는 **(a)** (필드 `motivic_realization`과 동일). `etale_eq_comb`는 rank–nullity를 거치지만 `hdefect`/`etale_realization` 공리가 내용 전부. | 예시 `abstractFibreOfData`(6535)는 `ℚ^a × ℚ^b`로 합성한 모델입니다. |
| `EtaleMotivicRealization` (7279) | `etale_eq_motivic`, `bump_eq_comb` | **(a)** | 비교 동형 `Het ≃ Hmot`과 `dim_Het = 2g+b₁+δ`를 가정합니다. 예시 `smoothEtaleMotivic`은 `ℚ^{2g}`와 `refl`입니다. |
| `EtaleLAdicH1` (7812) | `bump_eq_comb` (7833) `:= E.bump_eq`, `etale_bump_eq_motivic_jump`, `master_equivalence` | **(a)/A** | 필드 `bump_eq`가 결론입니다. 임의의 ℤ_ℓ-module을 "진짜 ℓ-adic étale cohomology"라고 부릅니다. |
| `ExtRealization` (7583), `SheafCohomologyComparison` (7600), `torHomology_zmodGcd_bypass`의 `kerComparison` (7572) | `iso_zmodGcd` 등 | **(a)** | 결론 동형을 필드나 가설로 받습니다. 예시는 모든 객체를 `ZMod gcd`, `Iso.refl`로 둔 것입니다. |
| `master_equivalence`의 `hmot : eulerChar N bZ = E.comb` (8341) | 위 표 #12 | **(a)** | `bX, bU, bZ`는 임의의 정수열입니다. "무조건부, 진짜 객체 사이"라는 문구는 사실이 아닙니다. |
| `LeftDerivedComputesResolutionH1` (5057) | 어디에서도 가설로 쓰이지 않음 | 미해소 open | 정직하게 Prop로만 두었습니다. 환원(6731, 6824)은 진짜 정리입니다. |
| `SublinearCohDensity` (1120, Conj 8.3.7) | 주장되지 않음 | 정직 | 유한 support 경우만 증명했습니다(4388). |

- **해소(d) 사례**:
  - `CurveData.ofSES`(1799)
  - `GoodRedCert.complete`(7058)
  - Tor 범주론 쪽 절반(`torLeftDerived_iso_resolutionHomology`)
  - 산술 핵심(`resolutionH1_kernel_iso`, 6809)
  - q=1 밀도(`apDensity_q1_genuine`, 7749)
- **"boundary 닫힘" Bool 표의 문제**: 여러 표가 Bool 상수로 순환 인터페이스를 "logicallyVerifiedBypass / bypassObjectRealized / closed / proven"으로 재라벨합니다.
  - 해당 선언: `masterIdentity_no_piece_absent`(6588), `etaleMotivic_all_bypassRealized`(7368), `cechExtFinal_all_bypassVerified`(7638), `delta52_all_closed`(8008), `delta54_both_extracted`(8277), `master_equivalence_all_proven`(8386), `hasse_bound_all_proven`(8503)
  - 이 정리들은 손으로 적은 `Bool` 값을 `rfl`/`decide`로 확인할 뿐이므로 **수학적 내용이 0**입니다. 그런데도 독자에게 "모든 경계가 해소됐다"는 인상을 줍니다.

## 5. 정의 충실도

- **Čech H¹**: `cechH1 := ZMod (gcd M N)`(464)는 `(a,b) ↦ Ma − Nb`의 cokernel과 증명된 동형으로 연결됩니다(468, 5134).
  - 그러나 이 차분은 ℤ 위 표시(presentation)입니다. Spec ℤ 위 sheaf의 Čech 복합체가 아닙니다.
  - `modularPadicSheaf`(3605)는 AU=AV=AUV=ℤ, ρ=×M, ×p^k로 정의되는데, docstring은 이를 "actual coefficient sheaf"라고 부릅니다. 과장입니다.
- **Tor/Ext**:
  - `Tor1Class`(576)와 `Ext1Class`(581)는 **문자 그대로 같은 타입** `ℤ ⧸ gcdSubgroup`입니다. `cech_tor_iso_real`과 `cech_ext_iso_real`도 같은 정의입니다.
  - `TorH1 := ker(×M on ZMod N)`(1380)와 `ExtH1 := coker(×M)`(7954)는 교과서적 계산 모델이고 값은 정확합니다.
  - Mathlib의 진짜 Tor(`leftDerived (tensorLeft …)`)와의 다리는 **절반만** 있습니다(5034). 마지막 동형(`LeftDerivedComputesResolutionH1`)은 open으로 남아 있습니다.
  - Mathlib의 `Ext`와는 **다리가 전혀 없습니다**. 그런데도 `ExtH1` docstring은 "derived-category Ext¹"라고 씁니다.
- **Spec ℤ**: `SpecZPoint`(104)는 곱셈 소수성만 요구하고 덧셈 닫힘은 요구하지 않습니다. 따라서 이데알이 아닌 점(예: "2∣f ∨ 3∣f")도 포함합니다.
  - 다리는 한 방향뿐입니다: `specZembed_preimage_D`(4619)로 D f ↦ `PrimeSpectrum.basicOpen`. 사용된 범위에서는 충분히 정직한 다리입니다.
- **primality sheaf**: `primalitySheaf`(3193)는 ℕ 위 상수 presheaf에서 네 술어 `A ≤ n`, `M ∣ n`, `p^k ∣ n−target`, `¬ n ∣ Δ`의 논리곱입니다.
  - `Nat.Prime`과 연결하는 정리는 **없습니다**.
  - "sheaf" 조건(gluing)은 상수 presheaf라서 자명합니다.
- **δ_coh**: `ArithDetectable`(819)의 값은 {1, ⊤} 중 하나뿐이라 성질이 자명합니다. §I2(2101–2125)의 "불변성" 3개는 `deltaCoh_congr`의 복제입니다.
- **곡선과 검출기**:
  - `DualGraph`(1711)는 숫자 세 개입니다. `FibreData.h1X`는 2g+b₁+Σδ로 **정의**되어 있어서 `bump_eq`(1750)는 정의상 성립합니다.
  - §Δ54(8210–8260)에서 `SimpleGraph` b₁가 진짜로 계산되지만(`graphFirstBetti_isTree`), 곡선에서 추출된 그래프는 아닙니다.
  - `deltaInvariantFromNormalization`(8157)은 임의 모듈의 `Module.length`입니다.
  - "Voevodsky DM motive"라는 `MotivicRealization`(8060)은 `(topDeg, betti : ℕ → ℕ)`일 뿐입니다.
  - `etaleCohomologyH`(7911)는 `ModuleCat ℤ_ℓ` 위 임의 Γ의 `rightDerived`이고, 예시는 Γ = 𝟭입니다. étale 내용은 0이고 **명명 과장이 심합니다**.
- **좋은 충실도 사례**:
  - `PadicLogP.plog`(5290)은 진짜 ℚ_[p] 급수입니다.
  - `Deep.projResolution`(4998)은 진짜 Mathlib 객체입니다.
  - `fec_gate_iff_reduction_isElliptic`(7676)과 `wDiscriminantGate_nonsingular`(2037)는 Mathlib `WeierstrassCurve`를 실제로 사용합니다.
  - §Δ39/§Δ58은 Mathlib `IsMinimal`/`HasGoodReduction` 래퍼입니다. 다만 ℤ 위 `ecGate`와 DVR 위 `HasGoodReduction`을 잇는 정리는 없고, `fec_mathlib_goodReduction_exact`(7684)는 서로 무관한 두 진술을 ∧로 묶었을 뿐입니다.
  - `cotangent_detector_agreement`(6180)은 Mathlib `formallyEtale_iff`를 쓰지만 곡선 fibre와 연결되어 있지 않습니다.

## 6. 실질 수학 내용

**진짜 논증이 들어 있는 부분(대략 줄 수):**
- Bézout/CRT 기반 Čech cokernel (338–440, ~100)
- Tor 위수 `card_ker_mulLeft` (531)와 `ExtH1_card` (7962)
- `gcd_eq_prod_primeFactors` (725)
- `finiteCover_glue_coprime` (1325, Finset 귀납)
- p-adic 절단 log valuation 계층 (1433–1702, ~270). `padicValNat_le_sub_two`, `truncatedLog_residual_valuation`
- `crt_ses_exact_mid` (2651)
- `Deep` 투사 분해와 QuasiIso (4841–5060, ~220)
- **수렴 p-adic log** (5221–5580, ~360). 비아르키메데스 tsum 경계와 극한 논증, 홀수 p에서 2k 잔차
- `moduleCatHomologyIsoKer` (7502)
- Hasse 대수 동치 (8412–8487)
- `SimpleGraph` Betti (8210–8260)
- `specZembed` 다리 (4602–4667)

**대략적 비율(줄 기준):**
| 구분 | 비율 |
|---|---|
| 진짜 수학(비자명 증명) | ~20% (약 1,700줄) |
| Mathlib 얇은 래퍼 (Hensel, Weierstrass, Néron, cotangent, L-series, Dirichlet 무한성) | ~5% |
| 순환·퇴화 인터페이스와 그 소비 정리 (GeometricDetectors, EtaleLAdicH1 등) | ~15% |
| 논문 번호별 재진술·중복 (3319–4400, 4408–4600 인증서 12종, 5089–5220 "sheaf form", 4개 이상 층에 걸친 같은 정리의 반복 포장) | ~30% |
| String/Bool 상태표와 boundary 재라벨 (`claimIndex` 5956–6128, 상태 inductive 27개, Bool 표) | ~10% |
| toy presheaf, 층(layer), δ_coh, 인증서 래퍼 등 자명 인프라 | ~20% |

수학 수준은 학부 대수/정수론과 기초 p-adic 해석이 상한입니다. 논문의 깊은 내용(étale/motivic 비교, 밀도형 Dirichlet, Hasse 정리, Néron 모델)은 하나도 형식화되지 않았습니다. 대신 이름표가 붙은 인터페이스로 대체되어 있습니다.

## 7. 수학적 정확성과 과장 표기

1. **`HasseTheorem`(2754)는 거짓 명제**입니다. 곡선과 무관하게 모든 cardEp를 정량합니다. 사용처는 없지만 "named input"으로 서술되어 있습니다.
2. `hasse_supersingular_satisfiable`(2759): docstring은 "`HasseTheorem`-style hypotheses are non-vacuous"라고 하지만, 증명하는 것은 `HasseBound 0 p`뿐입니다.
3. §Δ56의 제목은 "Hasse 부등식 자체를 무조건부로 증명"(8391)입니다. 실제로는 aₚ² ≤ 4p를 같은 값의 대수적 재진술과 동치로 보였을 뿐이고, 곡선의 Frobenius와 연결하지 않습니다.
4. `abLog_synchronization`(6863): docstring은 "log X − pⁿ log A = plog u"라고 주장하지만, Lean에는 log X나 log A가 정의되어 있지 않습니다. 진술은 `plog u`에 대한 것뿐입니다.
5. §Δ57(8505)은 "해석적 밀도 1/φ(q)를 genuine하게 닫음", "외부 입력 교체"라고 주장합니다. 실제로는 L-급수 **하한** 인용뿐이고, `DirichletDensityAP`는 여전히 미증명입니다. 같은 파일의 `claimIndex`(6014)도 Thm 8.3.6을 `externalInput`으로 둡니다. 서술이 자기모순입니다.
6. `goodFibre_dualGraph_b1_zero`(5658): docstring은 "smooth fibre ⟹ tree"라고 하지만, 진술은 리터럴 그래프 ⟨1,0,1⟩의 b₁ = 0입니다.
7. `sheafExt1IsCechH1_presentation`(5169): `E`는 임의의 타입이므로 "faithful stand-in 인증"이라는 설명은 동어반복입니다.
8. `etale_bump_eq_motivic_jump`(7934)의 "Weil cohomology 비교": 가설 `Et.comb = Mot.comb`에서 결론이 바로 나옵니다.
9. `claimIndex`의 `leanRef`는 String이고, 실제 선언 존재 여부를 검사하지 않습니다. "_indexed" witness는 리스트 멤버십만 확인합니다.
   - 일부 status는 부정확합니다. 예: Prop 2.5 → `good_locus_checklist`는 `.conditional`로 표시되었지만 실제로는 무조건부입니다.
10. 진술 자체의 수학적 오류(HasseTheorem 제외)는 발견하지 못했습니다. 무조건부 정리들은 모두 참이고 가설도 적절합니다. 다만 `padicValRat` 진술에 붙은 `≠ 0` 가설은 0의 valuation 관례 때문에 필요한 것으로 합리적입니다.

## 8. 코드 품질

- 8.7k줄 단일 파일입니다. 같은 결과가 §A–§P, §Q–§W, §Δ11–§Δ25(논문 번호별), §Δ26(인증서), §Δ30(sheaf form)에 걸쳐 3–5회 반복 포장되어 있습니다.
- 한국어와 영어 docstring이 섞여 있고, "boundary" 절이 §Δ36–§Δ58에 걸쳐 같은 주제(étale/motivic/Néron/Dirichlet)를 여러 번 "닫았다"고 되풀이합니다. 그때마다 Bool 상태표가 추가됩니다.
- 기타 문제:
  - import 중복: `Mathlib.NumberTheory.LSeries.PrimesInAP`가 71줄과 82줄에 두 번 있습니다.
  - axiom-audit section이 비어 있습니다.
  - 낡은 툴체인 주석이 있습니다(7660).
- 증명 자체는 대체로 짧고 견고합니다. `omega`, `linarith`, 명시적 rw를 쓰고, 취약한 대형 `simp`는 적습니다. heartbeat 상향은 1곳입니다.
- **Mathlib PR 후보**:
  1. `PadicLogP` 일체: 수렴 p-adic log, `plog_norm_le`, 2k 잔차. Mathlib에 p-adic log가 없다면 가치가 있습니다.
  2. `moduleCatHomologyIsoKer`: 일반적인 보조정리입니다. Mathlib에 유사한 것이 있는지 확인이 필요합니다.
  3. `LeftDerivedComputesResolutionH1`을 완성하면 "Tor₁^ℤ(ℤ/M, ℤ/N) ≅ ℤ/gcd" 예제가 됩니다.
  4. `padicValNat_le_sub_two`.

## 9. 컴파일 위험

- `build-logs/`와 `build-evidence/`에 Spt4 전용 로그는 없습니다. 파이프라인 계약 문서(`build-evidence/continuation/FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md`)에 13개 필수 파일 중 하나로 나열되어 있을 뿐입니다. 현재 HEAD의 컴파일 여부는 lead의 빌드 결과를 따라야 합니다.
- 사용된 최신 Mathlib 이름을 로컬 Mathlib 트리(업스트림 `8cbb95e6`과 동일)에서 grep으로 확인했고, 모두 존재했습니다:
  - `lucas_primality_iff`, `ProjectiveResolution.isoLeftDerivedObj`, `ChainComplex.quasiIsoAt₀_iff`, `exactAt_succ_single_obj`
  - `exists_isMinimal`, `hasGoodReduction_iff_isElliptic_reduction`, `hasGoodReduction_or_hasMultiplicativeReduction_or_hasAdditiveReduction`
  - `Nat.infinite_setOf_prime_and_modEq`, `LSeries_residueClass_lower_bound`, `not_summable_residueClass_prime_div`
  - `Module.length_eq_add_of_exact`, `Module.length_prod`, `isAddCyclic_of_surjective`, `addEquivOfAddCyclicCardEq`, `isElliptic_iff`, `ModuleCat.kernelIsoKer`
  - `norm_tsum_le_of_forall_le_of_nonneg`: `norm_tprod…`의 to_additive 버전으로 존재
  - `Algebra.formallyEtale_iff`: `@[mk_iff]`로 생성
- 위험 신호:
  - 4945의 heartbeat 상향(`rfl`).
  - 5507 주석: "`IsTopologicalAddGroup ℚ_[p]` instance is unavailable in this import context"라는 우회가 있어 import 구성에 민감합니다.
  - 그 밖의 뚜렷한 위험은 찾지 못했습니다. 컴파일 여부는 **확인 불가**입니다.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | **8** | sorry/axiom/native_decide 0, heartbeat 1곳, 트릭 없음. 단 `#print axioms` 근거가 없고 거짓 `HasseTheorem` 정의가 남아 있음. |
| 조건부 인증의 정직성(비순환성) | **3** | 핵심 기하 결과(Thm 7.1, Prop 2.5/3.26, master equivalence, étale=motivic)가 모두 "결론 = 필드"인 순환 인터페이스이고 예시는 0/refl로 퇴화. Bool 표로 "모두 닫힘"을 선언. 일부(`LeftDerivedComputesResolutionH1`, Conj 8.3.7)는 정직. |
| 수학적 실질성 | **4** | 수렴 p-adic log, 투사 분해/QuasiIso, CRT/Tor 계산은 진짜지만 초급~중급 수준. 깊은 내용은 형식화되지 않음. |
| 정의 충실도 | **3** | Čech/Tor/Ext는 presentation 프록시(Tor=Ext 같은 타입), primality sheaf는 소수성과 무관한 술어 곱, étale/motivic/DM은 임의 모듈과 ℕ 열. plog, ProjectiveResolution, Weierstrass 쪽은 충실. |
| 코드 품질·유지보수성 | **4** | 개별 증명은 깔끔하나, 8.7k줄 단일 파일에 3–5중 중복, 상태표 남발, 낡거나 빈 감사 절, 과장 docstring. |
| **종합** | **4** | 쓸 만한 p-adic/호몰로지 조각이 있지만, 논문 #4의 "étale–motivic–derived" 핵심은 순환 인터페이스로만 "인증"되어 있음. |

---

## 커버리지 로그

모든 구간을 `Read`로 순서대로 정독했고, 생략한 구간은 없습니다.

- 1–900: 헤더, §A0, §A, §B, §B1, §C, §D, §E, §E1, §F, §G, §H, §I, §J 시작
- 900–1700: §J, §K, §L, §M, §N, §O, §P, §A5, §A6, §A7, §E2–§E4, §K2, §K3
- 1700–2500: §M2–§M4, PART II §Q–§W, §X, §I2, §I3, §N2–§N4, §Y, §Z
- 2500–3300: §Z2, PART III §Δ1–§Δ10
- 3300–4100: §Δ10–§Δ19.4
- 4100–4900: §Δ19.5–§Δ29.1 (Deep 시작)
- 4900–5600: Deep, §Δ30 P4, §Δ31 PadicLogP, §Δ32 시작
- 5600–6300: §Δ32–§Δ37
- 6300–7000: §Δ37–§Δ42
- 7000–7600: §Δ42.2–§Δ48
- 7600–8200: §Δ48–§Δ54.1
- 8200–8714: §Δ54.2–§Δ58, 빈 axiom-audit 절, `end Spt4`

보조로 다음을 확인했습니다: 주석 제거 사본에서 키워드 grep, `decls_cls.json` 집계, Mathlib 이름 존재 여부 grep, `build-logs`/`build-evidence` 확인.
