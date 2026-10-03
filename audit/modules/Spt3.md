# Spt3 모듈 감사 보고서

대상 파일: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Spt3.lean` (7,506줄, 약 430 KB)
선언 규모(사전 집계): theorem 367, def/abbrev 약 155, structure 6, inductive 4, example 41
주석 비중: 주석·문자열을 지운 사본 기준 비공백 코드 줄은 4,011/7,507(약 53%)이고, 문자 수로는 주석이 압도적으로 많다.
감사 범위: 1–7506행 전체를 순서대로 읽었다(맨 아래 커버리지 로그 참조). `lake`/`lean`은 실행하지 않았다.

---

## 1. 목적과 논문 대응

- 대상 논문은 Lee Ga Hyun, "A Primality Sheaf and Global Certification"(spt3)이다(1–13행, 73–140행). 이 파일은 `Spt3.lean`, `Spt3Sheaf.lean`, `Spt3Cert.lean` 세 조각을 합친 뒤, 체크리스트 "Category A–Z"와 이후 추가분(T1/T2, PART 3/4/A/B/D)을 덧붙여 만든 통합본이다.
- 논문에서 대응시키는 항목(87–118행 §-map 기준):
  - 등화자 핵: (M)∩(N) = (lcm). Lem 5, §3.3/3.5
  - Zero-Class 규칙(교정판), thickness(Prop 7)
  - Tor₁(ℤ/M, ℤ/N) ≅ ℤ/gcd. Lem 6/12, Thm 4.1, Cor 2721
  - CRT 분해: Lem A/10/11, Thm 14, Rem 19
  - IC = Σ min·log q, |Tor| = exp(IC): Cor 2777, Lem 15/16
  - 비트 비용 상한: Prop 17
  - 안정성: Prop 8 / Cor 9
  - derived equalizer = cotangent test: Thm 20
  - 전역 단면 판정 "X prime ⇔ ∃ global section": Thm 1/18
  - Hensel/Jacobian 게이트: Prop 2
  - Baker 하한(③), p-adic log(②), 수치 창(⑧), 4층 sheaf amalgam(⑦)
- 파일 스스로 "교정"이라고 부르는 항목:
  - §3.4(3)의 gcd/min을 lcm/max로 바로잡음(120–129행, `paper_zeroClass_false` 866행)
  - A-3 포함 방향 반례(`ker_mono_dvd_false`, 848행)
  - B-5 삼중 cocycle(1135행)
  - p = 2 경계 결함(`padic_log_defect_p_two`, 1380행)

## 2. 헤드라인 정리

상태 표기: U = 무조건 진짜 증명, C = 명명 가설에 조건부, A = 접근자 투영, T = 자명·동어반복.

| # | 선언 (행) | 진술 요약 | 상태 |
|---|---|---|---|
| 1 | `Spt3.card_ker_mulLeft` (208) | `Nat.card (mulLeft (M : ZMod N)).ker = Nat.gcd N M` | U |
| 2 | `Spt3.ker_mulLeft_addEquiv` (369) / `tor_primewise_addEquiv` (2471) / `tor_primewise_directSum` (2622) | `ker(×M on ℤ/N) ≃+ ZMod (gcd N M)`, `≃+ Π/⨁_{q∣N} ZMod (q^min)` | U |
| 3 | `Spt3TorValue.tor1_obj_iso` (3372) | `(Spt3Tor.Tor (ℤ/M) 1).obj (ℤ/N) ≅ ModuleCat.of ℤ (ZMod (gcd M N))`. 직접 만든 사영 분해 `Spt3B1Resolution.resP` (3041)와 `isoLeftDerivedObj`를 거쳐 얻는 진짜 derived functor 값 | U (가장 실질적) |
| 4 | `Spt3TorValue.tor1_primewise_iso` (5882) | 진짜 Tor₁ ≅ `⨁_{q∣N} ZMod (q^{min(v_q M, v_q N)})` | U |
| 5 | `Spt3Tor.natTrans_leftDerived_add` (5917), `projectiveResolutions_additive` (2852), `torBif_additive` (5937) | leftDerived의 자연변환 가법성, 사영분해 functor의 가법성 | U (Mathlib PR 후보) |
| 6 | `Spt3.card_Tor_eq_exp_IC` (265), `IC_coprime_add` (292), `IC_eq_zero_iff_coprime` (889), `localized_intersection_ideal` (2583) | gcd = exp(IC), IC 가법성, IC = 0 ⇔ 서로소, 국소화 이데알 = (p^max) | U |
| 7 | `Spt3Cert.pocklington_prime` (3681), `pocklington_lehmer` (3863) | Pocklington(–Lehmer) 판정의 건전성(certificate ⇒ prime) | U |
| 8 | `Spt3Sheaf.RepointedConst_isSheaf` (4691), `predLayer_isSheaf` (4734), `amalgam_sheaf_isSheaf` (4789) | 재지정 상수 presheaf가 `Spec ℤ` 위 sheaf임(기약성 이용). 4층 amalgam도 sheaf | U (층 자체는 장난감 술어) |
| 9 | `Spt3PadicLog.padicLogSeries_summable` (4066), `padicLog1p_norm_le_self` (4265), `padicLogSeries_tendsto_zero_pk` (5713) | ℚ_p에서 log 급수 수렴, ‖log(1+x)‖ ≤ ‖x‖ | U |
| 10 | `Spt3Cert.theorem18_unconditional` (6072), `certification_iff_unconditional` (3537), `theorem18_tfae` (6004) | `X.Prime ↔ (True ∧ True ∧ True ∧ LucasCert X)` | T: Mathlib `lucas_primality_iff`를 다시 적은 것에 불과 |
| 11 | `Spt3.certification_iff_of_complete` (499) | `Hsound : FEC X → X.Prime`, `Hcomplete : X.Prime → (4층)` ⊢ `X.Prime ↔ (4층)` | C이지만 순환(결론의 두 방향을 가정함) |
| 12 | `Spt3Cert.prime_iff_section_of_complete` (785) | `AKSIsComplete FEC := ∀ X, X.Prime ↔ FEC X` ⊢ `X.Prime ↔ FEC X` | 순환 (`:= hFEC X`) |
| 13 | `Spt3.derived_equalizer_tfae` (333) (Thm 20) | `Hder : der = 0 ↔ smooth`, `Hgate : smooth ↔ gcd = 1` ⊢ TFAE | 순환·T (`der : ℕ`, `smooth : Prop`가 임의라서 내용 없음) |
| 14 | `Spt3.ec_prop2_unique_lift` (5462) (Prop 2) | `JacobianEtaleBridge (ZMod p) A jac` 가정 ⊢ 유일 lift | C, 사실상 순환 |
| 15 | `Spt3Baker.candidate_window_unique_nat` (5241) | 정수 후보에 대한 창 유일성(Baker 불필요) | U (초등적) |

## 3. 탈출구와 신뢰기반

- 주석과 문자열을 제거한 코드에서 `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`는 모두 0건이다. 리드 감사자가 확인한 사실과 일치한다. `set_option maxHeartbeats`도 없다.
- 커스텀 `elab`은 두 개다.
  - `#assert_only_safe_axioms` (7244)
  - `#assert_spt3_certified_safe_axioms` (7464)
  - 둘 다 `collectAxioms`로 허용 집합 {propext, Classical.choice, Quot.sound}를 강제한다. 구현은 정당하다.
  - 다만 감사 대상은 26개 선언(7428–7457, 7466–7491)뿐이고, 대부분 쉬운 산술 보조정리다. `tor1_obj_iso`, Pocklington, `RepointedConst_isSheaf`, p-adic 결과 같은 핵심 결과는 목록에 없다.
  - 그래도 위에서 본 대로 탈출구 토큰이 0건이므로 실질적 위험은 낮다.
- 빈 감사 섹션: "`#print axioms` audit at the end shows …"라고 주장하는 `section …AxiomAudit … end` 블록이 약 25개 있는데 모두 비어 있다(예: 646–647, 728–729, 788–789, 1584–1585, 2528–2529 …). 주석의 감사 주장은 해당 위치에서 실제로 실행되지 않는다.
- 연출성 필드: `Spt3CertificationBoundary.spt3Boundary`(7289)는 `trustedBoundary := True`, `noHiddenAxioms := True`로 정의되어 있고, `spt3Boundary_noHiddenAxioms := trivial`(7312)이다. 아무것도 증명하지 않는다.
- 같은 레코드의 `conditionalInputs`와 `globalCertificateClaim`은 글자 그대로 동일한 Prop이다(7292–7295).
- `Inhabited False`류 트릭, `Classical.choice`로 데이터를 날조하는 패턴, `default` 자리채움은 발견하지 못했다.
- 대형 `decide`:
  - `(by decide : ¬ Nat.Prime 25)`: 1493, 2790
  - `¬ Nat.Prime 4`: 1189, 1191, 3223
  - `(3 : ZMod 31)^30 = 1` 및 gcd 조건: 3990–3991
  - Mathlib의 `Nat.decidablePrime`은 `minFacAux`(`termination_by`로 정의된 WF 재귀, `Mathlib/Data/Nat/Prime/Defs.lean` 207–215)를 거친다. 따라서 25에 대한 커널 `decide`는 WF 축약에 의존하며, 버전에 따라 실패하거나 느릴 수 있다. 미확인 위험이다. 4는 `2 ∣ 4` 분기만 타므로 안전하다.
- 무해하지만 기묘한 명시적 인스턴스 가설: `padicLog1p_sub_trunc`의 `hTop : IsTopologicalAddGroup ℚ_[p]`(4292), `padicLogSeries_summable_nonarch`의 `hNA`/`hUnif`(5767). 실제 인스턴스로 충족되므로 공허하지는 않다.

## 4. 조건부 인증 감사 (핵심)

분류: (a) CIRCULAR, (b) SUBSTANTIVE, (c) SUSPECT-VACUOUS, (d) DISCHARGED.

| 가설·인터페이스 (행) | 정의 | 분류 | 근거 |
|---|---|---|---|
| `Spt3Cert.AKSIsComplete` (781) | `∀ X, X.Prime ↔ FEC X` | (a) | `prime_iff_section_of_complete := hFEC X`(786), `theorem18_of_any_complete := h X`(6081), `global_certificate_conditional`(7284), `prime_iff_verifier`, `prime_iff_ecpp`이 모두 결론을 그대로 가정한다. `AKSIsComplete_lucas`(3468)와 `_minFac`(3507)로 "충족"되지만, 그 내용은 `lucas_primality_iff`와 `Nat.prime_def_minFac`뿐이다. |
| `certification_iff_of_complete`의 `Hsound`/`Hcomplete` (499–504) | 결론의 ⇐/⇒ | (a) | 증명이 `⟨Hcomplete, …Hsound⟩`. 머리말 486행은 "가정하면 순환"이라고 스스로 경고해 놓고 그대로 했다. |
| `derived_equalizer_tfae`의 `Hder`/`Hgate` (333) | `der = 0 ↔ smooth`, `smooth ↔ gcd = 1` | (a) | `smooth`, `der`가 아무 수학 대상과도 연결되지 않은 자유 변수다. `C2_derived_equalizer_conditional`(2375)도 같은 재진술이다. |
| `Spt3Baker.BakerLowerBound` (4363) | `lb ≤ |Λ|` | (a) | `baker_window_clear := le_trans hwin hbaker`. 파일 스스로 "conjunction-introduction"이라고 공개했다(4453–4460). 정직하게 공개했지만 내용은 0이다. |
| `Spt3Baker.BakerSeparation` (5090) | `|Λ| < lb → Λ = 0` | (a)에 가까움 + (d) 부분 | `candidate_window_unique`은 이 가설과 log 단사성만으로 끝난다. 정수 후보에 대해서는 `candidate_baker_separation_proved`(5221)로 초등적으로 해소된다(d). 일반 실수 밑에 대해서는 사례별 가설이라 거의 결론과 같다. |
| `Spt3.JacobianEtaleBridge R A jac` (5443) | `jac ↔ FormallyEtale R A` | (a) | `ec_prop2_unique_lift`(5462)에서 `A`는 W와 무관한 임의의 `ZMod p`-대수다. `jac`이 참이므로 가설은 곧 "A는 formally étale"이고, 결론은 Mathlib `FormallyEtale.comp_bijective`다. 이름은 "Jacobian⟺étale 다리"지만 실체는 결론의 전제를 그대로 가정한 것이다. |
| `torDelta_naturality`의 `hcompat` (5545) | 결론식 ≫ mono ι | (a) | `cancel_mono`일 뿐이다. 이후 `torLES_delta_naturality`(5777)가 진짜 무조건 버전을 제공한다(d). |
| `Spt3Sheaf.amalgam_isSheaf`의 `hB : IsSheaf siteJ B` (1226), `Spt3Checklist.B4_amalgam_isSheaf_conditional` (2299), `Spt3FinalChecklist.sheaf_amalgam_is_sheaf` (3098) | 상수 presheaf ℕ가 sheaf | (c) 실제로 거짓 | 빈 열린집합 ⊥의 빈 덮개에서 유일성이 깨진다(ℕ은 singleton이 아님). 파일 스스로 4618행에서 "the plain constant presheaf B = const ℕ is NOT a sheaf"라고 인정한다. 세 정리는 공허하게 참이다. 이후 `RepointedConst`(4660)로 대체되어 무조건 sheaf 결과가 생겼다(d). 단 `inf_isSheaf`(1206) 자체는 일반적이고 진짜다. |
| `PowerSeries.LogInterface` (6352, class) | `logOf : A⟦X⟧ → A⟦X⟧` + 곱 가법성 | (c) 퇴화 | `logOf := fun _ => 0`으로 자명하게 인스턴스화되므로 log를 전혀 고정하지 않는다. `PowerSeries.logOf_mul`(6369)과 `Spt3PadicLogFormal.logOf_mul_qp`(6383)는 (A) 접근자다. "this branch does not expose logOf"(2054, 6337, 7376)라는 주장도 틀렸다. 고정된 Mathlib에 `PowerSeries.logOf`가 있다(`Mathlib/RingTheory/PowerSeries/Log.lean:82`, Spt3가 import하지 않았을 뿐). 형제 모듈 `Spt6.lean:7910`의 `PadicLogFormal.logOf_mul`은 무조건 증명되어 있다(모듈 간 해소). |
| `Spt3PadicLog.PadicLogAdditive` (4099) | ‖x‖, ‖y‖ < 1에서 log((1+x)(1+y)) = log(1+x) + log(1+y) | (b) | 참인 깊은 입력이다. 사용처: `padicLog_gate_sync`(=Hadd 재진술, 4110), `padicLog1p_starPow`(4195, 귀납으로 실제 증명). |
| `Spt3PadicLog.PadicLogLipschitz` (4103) | ‖log(1+x) − log(1+y)‖ ≤ ‖x−y‖ | (b) | 참이다. 유일한 사용처 `padicLog1p_norm_le`는 무조건 정리 `padicLog1p_norm_le_self`(4265)로 대체되었다. |
| `Spt3JacEtale.KaehlerConormalGap` (6657) | `Subsingleton Ω[R[X]/(f)/R] → IsUnit (f' mod f)` | (b) | 참이다(conormal 열). 증명 가능하지만 미완. |
| `Spt3TorHorseshoe.HorseshoeInductionStep` (6950) | epi 사상 SES의 핵이 SES | (b) | 참이다(snake). 이를 가설로 쓰는 정리는 없고 이름만 등록되어 있다. |
| `Spt3Cert.VerifierSound AKSPolyTest` (6155, 6172) | (X+1)^n = X^n+1 in (ℤ/n)[X] ⇒ n prime | (b) | 참이다(이항계수 판정). 미증명. |
| `ECPPCertSound` (6183) | `VerifierSound` 별칭 | (b)/형식 | 내용 없는 일반 술어다. |
| `cost_affine_bound`의 `hcost` (421) | 추상 비용 | (d) | `totalOps_cost_affine`(5598)로 해소되지만, totalOps가 바로 Σmin이라 정의상 자명하다. |
| `PocklingtonCert`, `PocklingtonLehmerCert` (3705, 3887) | 증거 필드 구조체 | 정상 | 실제 인증서 데이터다. 인스턴스 `pocklingtonCert7`(3742), `pocklingtonLehmerCert7`(3931)은 진짜 값(7 = 3·2+1, a=3)이다. |

참조 인스턴스·예제 점검:

- 수치 예제(24/1440, 147/2401, 7, 31, 25, 15 등)는 진짜 대상을 쓴다.
- 4층 `Fnum_layer`/`Fmod_layer`/`Fpadic_layer`(1468–1472)는 `1 < X`, 홀짝, mod 3 게이트로 장난감 수준이다. `FEC_layer := LucasCert`(1474)이고, 논문의 EC/AKS 층은 아니다(파일이 명시함).
- 결과적으로 "4층 sheaf amalgam이 소수 판정과 같다"(`concrete_four_layers_iff_prime`, 3112)는 실제로 LucasCert 한 층의 내용뿐이다. 나머지 세 층은 잉여다. `complete_layer_makes_others_redundant`(2797)가 이를 스스로 증명한다.

## 5. 정의 충실도

- Tor: 처음에는 `ker(×M on ZMod N)` 프록시였다. 이후 `Spt3Tor.Tor N n := Functor.leftDerived (tensorLeft N) n`(2844)를 도입했고, Mathlib `CategoryTheory.Tor`와 `rfl`로 같음을 보였다(`torBif_obj`, 5508). 다리 정리 `tor1_obj_iso`와 `tor1_primewise_iso`가 존재한다. 충실하다.
  - 다만 Category J/K 주석의 "Mathlib has NO module Tor functor"(2732–2736, 2812–2815)는 거짓이다. 파일은 60행에서 `Mathlib.CategoryTheory.Monoidal.Tor`를 import하고 5505행에서 사용한다.
- Site와 sheaf: `Opens.grothendieckTopology (PrimeSpectrum ℤ)`를 쓰고, `Subfunctor`와 `Presieve.IsSheaf`는 진짜다. 단 원래 ambient B(상수 presheaf)는 sheaf가 아니다(§4). `RepointedConst`(4660)는 사실상 `Spec ℤ` 위 상수 sheaf다. 층(layer) 내용은 장난감 술어다.
- p-adic log: `padicLog1p := ∑' padicLogSeries`(4074)는 진짜 tsum이다. 가법성은 가설로 남아 있다. 형식 log(`LogInterface`)는 퇴화했다(§4).
- Cotangent: `AffineTorAmpZero`(4518)는 `Projective Ω ∧ Subsingleton H1Cotangent`인데, 이것은 Mathlib의 `FormallySmooth` 정의 자체다. 그래서 R-1/R-2/R-3(4526–4560)은 정의를 펼친 것에 가깝다. 실질적 다리는 R-6 `torAmpZero_iff_infinitesimal_lifting`(4569)뿐이다.
- AKS: `AKSPolyTest`(6141)는 지수 시간 전차수 판정이고, 진짜 AKS(mod X^r−1)는 아니다. 파일이 명시한다. `AKSIsComplete`라는 이름은 실제로 "임의 술어의 완전성"을 뜻하므로 오도적이다.
- ECPP: `Spt3ECPP`(6229–6328)는 "ZMod N에서 비가역 분모가 약수를 드러낸다"는 초등 사실이다. "FIRST-TIME … partial group law" 표현은 과장이다. 실제 점 덧셈 좌표식이나 곡선 위 보존은 없고, 분모가 unit이냐 아니냐만 다룬다.
- Baker: `BakerLowerBound`/`BakerSeparation`은 내용 없는 자리표시자다. 정수 후보 경우는 초등적인 `log_nat_separation`(5202)으로 진짜 해결된다.
- EC good locus: `ec_goodLocus_formallyEtale`(6726)는 Mathlib `StandardEtalePair` 인스턴스를 적용한 것이다(`inferInstance`). 진술은 R[X] 위에서 맞다. 그러나 "D(∂W/∂Y) ⊇ D(Δ)"는 증명하지 않았고, `JacobianEtaleBridge`/`ec_prop2_unique_lift`와 연결하는 정리도 없다. "substantially discharges the multivariate side"(2104)는 과장이다.

## 6. 실질 수학 내용

진짜이면서 비자명한 증명:

- `card_ker_mulLeft`, `gcd_eq_prod_primeFactors`, `card_Tor_eq_exp_IC`, `IC_coprime_add`, `localized_intersection_ideal`
- `Spt3B1Resolution.resP` 구성(quasiIso 증명 포함, 3041–3059), `tor1_obj_iso`(homology 동형 연쇄), `tor1_primewise_iso`
- `projectiveResolutions_additive`(호모토피 유일성 이용), `natTrans_leftDerived_add`
- Pocklington 핵심 보조정리 `pocklington_dvd_sub_one`(3647, orderOf 논증), `pocklington_lehmer_dvd_sub_one`
- `RepointedConst_isSheaf`(기약성으로 unique gluing), `predLayer_isSheaf`
- p-adic log의 수렴성, 항별 노름 상계, 초거리 tsum 상계
- `fnum_log_window`, `log_nat_separation`, `abs_log_sub_ge/le`
- `crt_glue_finset`, `horseshoe_base_epi`, `range_crtDiagonal_eq_ker_crtObstruction`, `weierstrass_hensel_gate`(hensels_lemma를 Weierstrass y-다항식에 연결)

이들은 대부분 Mathlib 정리를 깔끔하게 조립한 중간 난이도 증명이다. 깊은 정리를 새로 증명한 것은 아니다.

비계(scaffolding)·재진술 비중(코드 줄 기준 대략치):

- `Spt3Checklist` 문자열 원장과 `rfl` 상태 정리, 래퍼(1608–2400): 약 675줄
- `Spt3FinalChecklist` 래퍼(3078–3256): 약 130줄
- Category M의 Theorem 18 재진술들: 약 150줄
- Baker Q/U 자리표시자: 약 150줄
- CertificationBoundary와 FutureWork 레지스트리(7253–7422): 약 110줄
- 방화벽 약 70줄, 빈 감사 섹션 약 75줄
- 비계 합계는 코드 4,011줄 중 약 1,350줄(약 35%)이다. 나머지 약 65% 가운데 진짜 비자명 증명은 약 2,000–2,400줄(코드의 50–60%)로 추정하고, 그중 "깊은" 부분(Tor 값 계산, 가법성, Pocklington, sheaf)은 약 800줄이다.
- 파일 전체 문자 기준으로는 주석이 대부분이라서 실제 수학이 차지하는 비중은 훨씬 작다.

논문 핵심 주장(소수성을 sheaf 단면으로 판정하는 비자명한 기준) 자체는 실질적으로 형식화되지 않았다. Theorem 18의 "무조건" 판은 Lucas-Pratt 재진술이고, Thm 20은 순환 TFAE다.

## 7. 수학적 정확성과 과장

- 머리말과 본문이 모순된다.
  - 131–138행: "we do NOT certify prime ⇔ certificate", "p-adic log bridge and EC/étale … omitted"
  - 뒤의 `theorem18_unconditional`(6072), `C1_theorem18_scope`(1897–1911): "PROVED unconditionally"
  - `paperClaimStatus`(7328): "Global-section certification … conditional"
  - 7266–7268행: "the prime ↔ section equivalence is never asserted unconditionally". 그런데 실제로는 (Lucas 판으로) 무조건 단언했다.
- "Theorem 18 FULLY UNCONDITIONAL"(6068–6074)은 `X.Prime ↔ True ∧ True ∧ True ∧ LucasCert X`다. 논문 정리라기보다 Mathlib `lucas_primality_iff`를 다시 적은 것이다. 문서는 이를 "provably UNNECESSARY AKS"라고 포장한다.
- "the `smooth ↔ der=0` bridge this discharges"(`thm20_bc_affine_tfae`, 4549–4552): `derived_equalizer_tfae`의 자유 변수 `smooth`, `der`와 아무 연결이 없다. 따라서 해소하지 않았다.
- `B18`/`ec_goodLocus_formallyEtale`: "D(∂W/∂Y) ⊇ D(Δ)"는 미증명이고, 다리 해소 주장은 과장이다(§5).
- "FIRST-TIME … partial group law"(6202–6227, 2029): 과장이다(§5).
- 수치 불일치: "six conditional Prop interfaces"(7335) 대 `futureWork_count = 7`(7414). "Mathlib v4.31.0"을 반복 표기하지만 툴체인은 v4.33.0-rc1이다.
- 교정 주장(min/max)은 수학적으로 옳다(`paper_zeroClass_false`, `paper_min_intersection_reading_is_false`). 이 점은 긍정적이다.
- `triple_cocycle`(1135)의 반례 주석(a=2, b=1, c=3, …)은 진술(b ∣ s₁−s₃)과 맞는다.

## 8. 코드 품질

- 7.5k줄 단일 파일이고 "Category A–Z, part n, T1/T2, PART 3/4/A/B/D" 식으로 덧붙여 쌓은 구조다. 같은 결과가 여러 번 재노출된다. 예: `kernel_mem_iff_lcm` = `overlap_glue_iff_lcm`, `ker_mulLeft_addEquiv_prod` = `ker_additivity_coprime`, `gcd_primepow_eq` ≈ `gcd_primePow` ≈ `gcd_primepow_overlap` ≈ `factorization_gcd_prime_pow`, `crt_equalizer_compat_iff` ≈ `exists_modEq_and_modEq_iff_gcd_dvd_sub`, `ModZ` 두 번 정의, `Fpadic_pred`/`Fmod_pred` 미사용.
- 주석이 낡았거나 모순된다: §7, Tor 부재 주장, `LogInterface` 근거.
- "Spt3 log collision" 배치 수정(commit `e52217bf`, final-authority-bot)은 `def PowerSeries.logOf`를 `interfaceLogOf`로 바꿔 Mathlib의 `PowerSeries.logOf`(Spt6가 import)와 이름 충돌을 피한 것이다. 수정 자체는 맞다. 그러나 다음 문제가 남는다.
  - (i) 정리 이름 `PowerSeries.logOf_mul`은 그대로라서 Mathlib 네임스페이스를 오염시키고, 향후 Mathlib에 같은 이름이 생기면 충돌한다.
  - (ii) 6337행과 7376행 문서의 "branch lacks logOf" 근거는 interfaceLogOf 독스트링("Mathlib's global PowerSeries.logOf")과 모순된다.
  - (iii) Spt6가 이미 무조건 증명을 갖고 있으므로 인터페이스 자체가 불필요하다.
- 견고성: `maxHeartbeats` 상향은 없다. `decide`로 소수성을 판정하는 부분은 위험 요소다(§3).
- Mathlib PR 후보로 가치 있는 것:
  - `natTrans_leftDerived_add`
  - `projectiveResolutions_additive`(Mathlib의 LeftDerived.lean과 Resolution.lean에서 해당 인스턴스를 찾지 못함)
  - `torBif_additive`
  - `range_crtDiagonal_eq_ker_crtObstruction` / `crtObstruction_surjective`
  - `exists_modEq_and_modEq_iff_gcd_dvd_sub`(기존 Mathlib 존재 여부는 미확인)
  - `log_nat_separation`, `real_div_max_le_abs_log_sub`
  - Pocklington–Lehmer
  - `kerTransport`류 소도구

## 9. 컴파일 위험

- `build-logs/`, `build-evidence/`에서 Spt3 개별 컴파일 로그는 찾지 못했다. `FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md`에 13개 필수 파일 목록으로만 등장한다. 현재 head의 컴파일 여부는 근거가 없으며, 리드 감사자가 따로 확인 중이다.
- 위험 요소:
  - WF 재귀 `minFacAux`를 거치는 `decide`(¬Nat.Prime 25: 1493, 2790)
  - 마지막 수정 커밋(e52217bf)에서 rename을 했지만, 하위 사용처 `logOf_mul_qp`가 함께 수정되어 일관성은 있다.
  - 대규모 `simp`/`aesop_cat`(3051–3052)과 `rfl`로 범주론 객체 동일성을 보이는 부분(`torBif_obj`, `torBif_map`, `torFirstVar_obj`)은 Mathlib 내부 정의 변화에 취약하다.
  - `padicLogSeries_summable_nonarch`의 `@...` 명시 인스턴스 인자 나열(5773–5774)은 시그니처 변화에 취약하다.
- 확정적인 오류 증거는 없다.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 8 | sorry/axiom 0, 방화벽 elab 정당. 다만 방화벽 범위가 좁고, 공허한 `hB` 정리가 있으며, `decide` 위험과 컴파일 증거 부재가 있다. |
| 조건부 인증의 정직성(비순환성) | 4 | AKSIsComplete, certification_iff_of_complete, derived_equalizer_tfae, BakerLowerBound, JacobianEtaleBridge, torDelta 등 순환 가설이 다수이고, 거짓 hB 가설이 있다. "무조건 Theorem 18"은 Lucas 재진술이고 원장끼리 모순된다. 반면 일부 공개(4453행 등)는 정직하다. |
| 수학적 실질성 | 6 | 진짜 Tor₁ 값 계산과 n-fold 분해, Pocklington–Lehmer, ℚ_p log 수렴, 재지정 sheaf는 실질적이다. 논문 핵심(sheaf 소수 판정, Thm 20)은 비어 있다. |
| 정의 충실도 | 6 | Tor, site, sheaf, tsum은 Mathlib 실객체이고 프록시와 다리가 연결되어 있다. 층 술어는 장난감 수준이고, LogInterface는 퇴화했으며, AffineTorAmpZero는 정의를 펼친 것이다. |
| 코드 품질·유지보수성 | 4 | 7.5k줄 덧붙이기 구조, 중복 래퍼, 빈 감사 섹션, 낡고 모순된 주석과 버전 표기. 그래도 개별 증명은 읽기 쉽고 PR 후보가 몇 개 있다. |
| 종합 | 5.5 | 대수와 정수론 하부구조는 진짜이고 양질이다. 그러나 "조건부 인증"의 헤드라인(Thm 18, Thm 20, Prop 2, Baker)은 순환이거나 동어반복이다. |

가장 중요한 단서: 이 파일에서 이름이 붙은 "깊은 가설"들의 상당수(`AKSIsComplete`, `Hsound`/`Hcomplete`, `Hder`/`Hgate`, `BakerLowerBound`, `JacobianEtaleBridge`)는 결론을 그대로 또는 거의 그대로 가정한다. 이것들이 "충족되었다"는 것도 Mathlib `lucas_primality_iff`를 다시 적은 데 불과하다. 따라서 "Theorem 1/18 무조건 증명"은 논문 고유의 수학을 전혀 검증하지 않는다. 실질적 가치는 Tor/CRT/IC 부분, Pocklington, p-adic 수렴, 재지정 sheaf에 있다.

---

## 커버리지 로그

다음 범위를 순서대로 Read했다(누락 없음): 1–700, 700–1399, 1399–1999, 1999–2598, 2598–3147, 3147–3696, 3696–4245, 4245–4794, 4795–5343, 5344–5892, 5893–6391, 6392–6840, 6841–7240, 7240–7506.

- 기계적 부분도 생략 없이 읽었다. 원장 문자열(1638–2141)은 내용 주장만 확인했다.

추가 확인:

- `Mathlib/RingTheory/PowerSeries/Log.lean`: `PowerSeries.logOf` 존재(82행), `logOf_mul` 없음
- `Spt6.lean:7861–8022`: `PadicLogFormal.logOf_mul`
- `git show e52217bf`: log collision 수정 diff
- `Mathlib/Data/Nat/Prime/Defs.lean:162–215`: `decidablePrime`, `minFacAux` WF
- Mathlib `LeftDerived.lean`/`Resolution.lean`: `projectiveResolutions` 가법 인스턴스 부재
- build-logs와 build-evidence에서 Spt3 언급 검색
