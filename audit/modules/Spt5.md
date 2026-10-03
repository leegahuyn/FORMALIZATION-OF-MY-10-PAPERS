# Spt5 감사 보고서

대상 파일: `/home/user/leegahuyn/mathlib4/PrimalitySheafVerification/Spt5.lean` (8,071줄. 1–430줄은 import 이전의 헤더 주석)
선언 통계(decls_cls.json 기준): 745개 = theorem 516, def 161, abbrev 14, structure 23, instance 7, example 24. accessor 판정은 5개, 3줄 이하 theorem은 51개.
주석·공백을 뺀 코드 줄은 4,055줄이고, 그중 243줄이 `#assert_only_safe_axioms` 호출이다.
`lean`/`lake`는 실행하지 않았다(브리프 지시). 컴파일 여부는 직접 확인하지 않았다.

---

## 1. 목적·논문 대응

- 대상 논문: Lee Ga Hyun, "Principal-Open Methods on Arithmetic Curves: From Equalizer–Tor to Supersingular Dichotomy"(1–6행).
- 헤더(23–413행)에 §-by-§ 대응표가 있다. 주장하는 대응은 다음과 같다.
  - §2/§3.2: 단축 Weierstrass 판별식과 profile 모델의 좋은 환원.
  - §2.1 Profile Box(IV.2, IV.6): equalizer clearance, CRT residue avoidance.
  - §2.2: Frobenius trace 점화식 `aSeq`, Legendre 점 개수 `ecPointCount`.
  - §9.3 Claim 9.1: supersingular/ordinary dichotomy와 Deuring 판정.
  - §5.2: étale p-torsion. 논문의 `(ℤ/p)²`를 `ℤ/p`로 고쳤다(C-3).
  - Theorem B / 9.2: `Tor₁(ℤ/M,ℤ/N) ≅ ℤ/gcd`.
  - §(4): thickness. 논문의 min/max 오류를 고쳤다(C-1).
  - §5.x / Ch 8: benchmark `x^{pn}+y^A`의 τ_p(C-2)와 Tjurina 길이.
  - Theorem A / 3.1 / 9.1: Master Equivalence. 검출기 Geom/Alg/Der/Ét/Mot.
  - §6.1–6.2: defect complex.
  - §7.1–7.2: Tate 모듈 Frobenius와 L-factor.
  - §2.1 AB-linearization과 p-adic log.
  - Standing Setup 2.1/2.2: principal-open site와 four-layer fibre product.
  - Ch 5: Frobenius 표(p ≤ 113), Hasse/Weil.
  - Section 6: transfer(A3).
- 정리 번호로 명시된 것은 Thm A(3.1/9.1), Thm B(9.2), Claim 9.1, T1.3, T2.1–2.4, T3.1–3.9, T4.1–4.2이다.

## 2. 헤드라인 정리 목록

표기: (U) 무조건 진짜 증명, (C) 명명된 가정에 조건부, (A) 접근자 사영, (T) 자명·동어반복.

| 행 | Lean 이름 | 진술(요약) | 상태 |
|---|---|---|---|
| 545 | `profile_goodReduction` | `Prime p → 5 ≤ p → ¬p∣A → goodReduction (-p) A p` | U (초등) |
| 644 | `exists_avoiding_residues` | 쌍마다 서로소인 `m i ≥ 2`, 금지 잉여 `r i`에 대해 `∃ y, ∀ i, (y:ZMod (m i)) ≠ r i` (CRT) | U |
| 1163 | `ecPointCount_eq_geometric` | `p ≠ 2`이면 χ-개수 = `1 + Σ_x #{y : y² = f x}` | U (Legendre 개수를 실제 개수에 연결하는 진짜 다리) |
| 1645 / 1676 | `card_ker_mulLeft`, `kerMulLeftAddEquiv` | `Nat.card ker(·M : ℤ/N) = gcd N M`, `ker ≃+ ZMod (gcd N M)` | U. "Tor₁"은 ker로 모델링했고 Mathlib Tor와의 다리는 없음 |
| 1750 | `kerMulLeftEquivPiPrimePow` | `ker ≃+ Π q, ZMod (q^min(v_qM, v_qN))` | U |
| 2723 | `Tjurina.quotientDimensionGoal_unconditional` | 모든 체 k, char p, Model에 대해 `Module.length k (k[x,y]/(f,f_x,f_y)) = tau p M` (⊤ 경우 포함) | U (실질적) |
| 3555 / 3573 | `HypersurfacePresentation.cokerEquivKaehler`, `.jacobianFullRank_of_formallySmooth` | `coker(jacobianMap) ≃ₗ Ω[S⁄k]`, `FormallySmooth k S → (fx,fy) = ⊤` | U (실질적) |
| 3869 | `grounded_master_tfae` | `[Smooth, FormallySmooth, JacobianFullRank, H1cotangent=⊥, cotangentBump=0].TFAE` | "UNCONDITIONAL"로 표기됐지만, 구조체 `B`의 `projective : Module.Projective S Ω` 필드에 사실상 조건부. 4절 (c)/(a) 참고 |
| 4035 | `FullMasterDetectors.masterTFAE` | 위 TFAE에 étale `bump=0`과 motivic `δ_total=0`을 더한 7-검출기 TFAE | C. 가정 필드 `etale_iff`, `Hmot`이 곧 결론의 두 다리라서 순환 |
| 4824 / 4857 | `norm_padicLog_sub_self_le`, `norm_padicLog_mul_sub_le` | p≥3, ‖u‖≤p⁻¹에서 `‖log(1+u)−u‖ ≤ ‖u‖²` 및 2차 곱셈성 | U |
| 4568 | `traceGenFun` | `(Σ aSeq a p r Tʳ)(1−aT+pT²) = 2−aT` (ℚ⟦T⟧) | U |
| 5606–5687 | `hasse_univ_F5/F7/F11/F13` | 각 p ∈ {5,7,11,13}의 모든 곡선에서 `ecTrace² ≤ 4p`(`decide`) | U (유한 계산) |
| 6383 | `weilGeometric_x3mx_F25` | 직접 센 `#E(𝔽₂₅) = 32 = 25+1−a_{p²}` | U (곡선 하나에 대한 계산) |
| 6865 | `abs_aPowTrace_le` | `aₚ² ≤ 4p → |a_{pʳ}| ≤ 2(√p)ʳ` | U (초등 복소해석) |
| 5472 / 6519 | `EllipticArithmeticData.masterTFAE`, `ConditionalCertificate.masterTFAE` | geomSS ⟺ aₚ=0 ⟺ p∣aₚ ⟺ `#G = 1` | C. `deuring` 필드가 사실상 결론 자체라 순환. 인스턴스는 모두 `Iff.rfl`/tautological |
| 2775 | `derived_equalizer_tfae` | `Hder : der=0 ↔ smooth`, `Hgate : smooth ↔ gcd=1`을 가정하고 세 명제의 TFAE를 결론 | T/순환 |

## 3. 탈출구·신뢰기반

- 주석과 문자열을 걷어낸 코드에서 `sorry`, `admit`, `axiom`, `native_decide`, `opaque`, `unsafe`, `implemented_by`는 0건이다(리드 확인과 일치).
- `set_option`(maxHeartbeats, maxRecDepth 포함), `macro`, `syntax`는 0건이다. 코드에 `#print axioms`는 없다(주석에만 언급).
- 사용자 정의 `elab`은 두 개다.
  - `#assert_only_safe_axioms id`(7754행): `collectAxioms`의 결과가 `{propext, Classical.choice, Quot.sound}`를 벗어나면 `throwError`로 빌드를 실패시킨다. 설계는 올바르다.
  - `#assert_all_local_safe_axioms`(7769행): `env.constants.map₂`를 순회해 이 모듈에서 추가된 상수를 전부 검사한다.
    - 핀 고정된 v4.33.0-rc1 소스를 확인했다. `Environment.constants`는 `toKernelEnv.constants`이고, 주석에 따르면 `map₂` 순회는 커널 검사가 끝날 때까지 블록된다. 따라서 비동기 증명도 포함된다.
    - `n.isInternal`(이름의 어느 부분이든 `_`로 시작)인 이름은 건너뛴다. 그래서 `_private...` 이름인 `private theorem`(예: `y_mul_pred`, 2326행)은 직접 검사되지 않는다. 다만 공개 정리가 이를 사용하므로 `collectAxioms`의 전이적 추적으로 실질적으로 덮인다.
    - 결론: 방화벽은 주장한 대로 작동한다(비공허).
  - 다만 두 가지 흠이 있다.
    - `cnt`를 세기만 하고 출력하지 않는다. 헤더(19행)의 "785개 Spt5.* 결과 검사"라는 수치는 코드로 검증할 수 없다. JSON 집계상 최상위 선언은 745개이고, 자동 생성된 `.mk`/`.rec` 등을 더하면 더 많다.
    - "sorry/native_decide 탐침으로 비공허성 검증"(21행)의 탐침 코드는 파일에 없다.
- `Inhabited`/`default`/`Classical.choice`로 데이터를 날조한 흔적은 없다.
- 대신 "자리표시 인스턴스" 패턴이 광범위하다(4절).
- `decide` 사용은 48곳이다. 큰 것으로는 `hasse_univ_F13`(169개 곡선 × 13항 Legendre 합, `IsSquare` 탐색 포함), `benchmark_table`(2760행), `ecCardF25_eq`(625쌍) 등이 있다. 모두 커널 `decide`이고 공리 위험은 없지만 빌드 시간 위험이 있다(9절).

## 4. 조건부 인증 감사 (핵심)

분류: (a) 순환, (b) 실질적 외부 입력, (c) 공허 의심, (d) 파일 내에서 증명됨.

| 가정/구조 (행) | 내용 | 분류 | 비고 |
|---|---|---|---|
| `HasseBound p ap` (1531) | `ap² ≤ 4p` | (b) | 진짜 Hasse 정리. p=5,7,11,13에서는 유한 계산으로 해소. 일반 p는 미해소 |
| `IsWeilPointCount ap p N` (1268) | `∀ r≥1, aPowTrace = pʳ+1−N r` | (b→사실상 무내용) | `N`은 임의 함수라서 술어가 N을 aₚ로 강제할 뿐 기하적 내용이 없다(파일도 6402행 `isWeilPointCount_iff_trace_formula`로 인정). 증인(6346, 6779, `B2_tautological_weil_shadow` 5872)은 전부 동어반복. r=2 기하 검증은 `y²=x³−x/𝔽₅` 하나뿐 |
| `DeuringData` (993) | `geomSS : Prop`, `deuring : geomSS ↔ p∣ap` | (a)/무내용 | `geomSS`가 임의 Prop이고, 정의된 인스턴스는 `operational`(1033)에서 `geomSS := p∣ap`, `Iff.rfl`뿐 |
| `EtalePTorsionData` (1055) | `G`, `iso : G ≃+ etalePTorsion p ap` | (a) | 모델 자체가 `ZMod (if p∣ap then 1 else |p|)`로 결론을 정의에 박아 넣었다. 인스턴스는 `tautological`(1102)에서 `iso := refl` |
| `FrobeniusEndoData` (1446) | `tr`, `deg`, `deg = p`, `#E = 1 − tr + deg`, `good` | 무내용 | 필드가 `tr = ecTrace`를 강제한다. Frobenius 자기사상과의 연결이 없다(정직하게 문서화됨) |
| `TateModuleFrobeniusData` (4239) | `frob_matrix : toMatrix frob = frobCompanion` | (b)의 형식, 내용은 행렬 대수 | `tautological`(4286)만 존재. V.3 감사(4295–4330)가 이를 스스로 인정한 점은 칭찬할 만하다 |
| `MasterDetectors` (3631) | `smooth_iff`, `cotangent_iff`, `bump_iff` | (a) | 세 필드가 결론 TFAE의 각 다리다. `ofHypersurface`(3691)가 두 개는 (d)로 해소하고 `bump_iff`는 가정으로 남는다. `MasterDetectors.trivial`(6453)은 `smooth := True`, `fx=1`, `fy=0` |
| `HypersurfacePresentation.projective` (3146) | `Module.Projective S Ω[S⁄k]` | (c)에 가까운 숨은 가정 | 아래 상세 |
| `HypersurfaceDetectors.etale_iff` (3887) | `etaleBump = 0 ↔ FormallySmooth` | (a) | 결론 다리 그 자체. `grounded`(3911)는 `etaleBump := if cotangentBump=0 then 0 else 1`이라는 지시함수로, étale과 무관 |
| `FullMasterDetectors.Hmot` (4027) | `etaleBump = fibre.deltaTotal` | (a) | `grounded`(4051)의 fibre는 `⟨V=0, E=지시함수, c=0, δ=0⟩`라는 퇴화 그래프. "BOTH external slots DISCHARGED"는 과장이다 |
| `FibreCombinatorics` (3942), `DefectComplex` (4343), `GroundedDefect` (4447) | 자유 자료 `(V,E,c,deltas)`, `rank_eq` | 무내용·모델 | `smoothWitness`(4473)는 `H := PUnit`. `IsAcyclic := rank = 0`. `ofGraph`/`graphBetti1`(4134–4170)은 진짜 그래프 이론(트리이면 b₁=0, d) |
| `ConditionalCertificate` (6465) | 8개 외부 의존을 한 구조체에 모음 | 대부분 (a) | `example5`(6566)는 Deuring `Iff.rfl`, étale/Tate tautological, `MasterDetectors.trivial`, fibre `⟨1,0,1,0⟩`로 모두 퇴화. 게다가 docstring이 틀렸다(7절) |
| `EllipticArithmeticData` 인스턴스 (5517–5700) | `exampleSS5`, `exampleOrd5`, `exampleCurveX3mX`, `ofCurveF5/7/11/13` | Hasse는 진짜 계산(d), 나머지 필드는 퇴화 | "ZERO trust surface"(5317, 5329)는 Deuring을 정의로 우회한 결과일 뿐이다 |
| `A3Transfer.TransferData` (7598) | `h1EtaleZero_to_gluing : h1EtaleZero → signature.Passes` | (a) | 양쪽 모두 자유 필드. `tautological`(7710)은 `ZMod 1`, `True`, `tr := 0`. 파일 스스로 "CONDITIONAL / not representative"라고 표기 |
| `cotangent_detector_tfae` (2853), `derived_equalizer_tfae` (2775) | 가정 `Hsm`/`Hder`/`Hgate` = 결론 다리 | (a) | 앞의 것은 3597행에서 (projective 필드 조건 아래) 해소. 뒤의 것(헤더상 "Thm A (CONDITIONAL)")은 순수 순환 |
| `A4ABBridge...of_shadow` (4954) | `hshadow`가 곧 결론 | (a) | 파일 스스로 "representative 아님"이라고 명시 |

### 핵심: `HypersurfacePresentation.projective` 필드 (3136–3146)

- "UNCONDITIONAL"이라고 홍보되는 Theorem A 검출기 TFAE 전부가 이 필드에 의존한다.
  - 헤더 196–198행: "TFAE with NO hypotheses".
  - `cotangent_detector_tfae_uncond`(3597), `jacobianFullRank_iff_formallySmooth_uncond`(3580), `grounded_master_tfae`(3869), `GroundedDetectors.ofHypersurface`(3827).
- 구조체가 `Module.Projective S Ω[S⁄k]`를 필드로 요구하고, `formallySmooth_iff_h1cotangent_eq_bot`(2981)이 이를 사용한다.
- 반례로 나는 노드 `k[x,y]/(xy)`를 직접 손계산했다. 컴파일로 확인한 것은 아니다.
  - 여기서 `fx = y`, `fy = x`이다.
  - `H1cotangent = Ann(y) ∩ Ann(x) = (x)∩(y) = 0`이다.
  - 그런데 Jacobian 이데알 `(x,y) ≠ ⊤`이므로 매끄럽지 않다.
  - f는 영인자가 아니므로, 이 곡선에 `HypersurfacePresentation.ofNeZero`를 만들지 못하게 막는 것은 `hproj`(Ω 사영성)뿐이다.
- 따라서 논문의 (Der) 검출기 "H¹(L_{X_p}) = 0 ⟺ smooth"는 축소된 초곡면에서 일반적으로 거짓이다.
- 형식화는 이 오류를 C-1~C-3처럼 "정정"으로 드러내지 않았다. 대신 Ω 사영성을 구조체 필드로 넣어 우회하면서 "NO external input"이라고 표기했다.
- 이 조건은 완전히 공허하지는 않다. 예: char 2의 `k[x,y]/(x²)`는 Ω가 자유인데 H¹ ≠ 0이다. 그러나 "H¹=0 ⟹ smooth" 방향의 실질 내용 상당 부분을 이 필드가 공급한다.
- `A2Genus.der_detector_general`(7225)은 Mathlib의 `FormallySmooth ↔ H¹=0 ∧ Projective Ω`를 그대로 재진술한다. 이것이 오히려 올바른 진술이고, 논문의 (Der) 다리가 Ω 사영성 없이는 성립하지 않음을 보여준다.

### "실제 대상을 담은" 인스턴스

- 실제 대상을 담은 것은 `ecTrace`(실제 Legendre 개수), `hasse_univ_*`(실제 곡선군 전체), `ecCardF25`(실제 𝔽₂₅ 위 곡선)뿐이다.
- 기하적 Deuring, étale, Tate, motivic, defect, transfer 인스턴스는 전부 퇴화(동어반복·지시함수·PUnit·ZMod 1)다.

## 5. 정의 충실도

충실한 것(Mathlib의 실제 개념 사용):
- `shortW`/`generalW` → `WeierstrassCurve`, `IsElliptic`, `Δ`, `Affine.Nonsingular`(709–842).
- `Algebra.H1Cotangent`, `Extension.cotangentComplex`, `Ω[S⁄k]`, `Algebra.FormallySmooth`/`Smooth`(3127–3616).
- `Module.length`(Tjurina, δ), `SimpleGraph.IsTree`(4140), `PrimeSpectrum`(`residualFibre`, 1838), `PowerSeries`, `RatFunc`, `ℚ_[p]`/`ℤ_[p]`, `hensels_lemma`.
- `cyclicPresheaf : DvdSiteᵒᵖ ⥤ RingCat`(6935)은 진짜 함자다.

프록시와 다리 여부:
- `IsSupersingular p ap := p ∣ ap`(886): 조작적 정의. 기하적 정의와의 다리는 없다(`DeuringData`로 외부화). 정직하게 명시됨.
- `etalePTorsion := ZMod (if p∣ap then 1 else |p|)`(916–920): 결론을 정의에 내장했다. `card_etalePTorsion_ordinary`, `etalePTorsion_isAddCyclic` 등은 정의를 푼 것에 불과하다. 실제 `E(F̄_p)[p]`와의 다리는 없다.
- "Tor₁(ℤ/M,ℤ/N)"은 `ker(mulLeft M : ZMod N)`로 모델링했다. 표준적 동일시이지만 Mathlib Tor와의 정리 수준 다리는 없다.
- `F_EC := kerLayer Δ` 등 네 개 층(7122–7133): 임의 모델이다. 정수 Δ를 곱하는 사상의 핵을 "타원곡선 정칙성 층"이라 부를 근거가 없다.
- 순환 "구조층" `O(D(n)) = ℤ/n`(5234–5299, 6907–6970): 오표기다. Spec ℤ에서 ℤ/n은 D(n)이 아니라 닫힌 부분스킴 V(n)의 좌표환이고, `O(D(n)) = ℤ[1/n]`이다. 5236행의 "`D(ab) = D(a) ∪ D(b)`"는 거짓이다(파일 자신의 `principalOpen_inter`(5118)가 `D(a)⊓D(b) = D(ab)`). 수학적 내용은 CRT 그 자체다.
- `cotangentBump := Module.length (H1cotangent)`(3751): "étale bump"의 대체물이라고 하지만 H¹=0 검출기의 재명명이다.
- `FibreCombinatorics.b1 := E + c − V`는 자유 자료다. `ofGraph`로 진짜 그래프에 연결된다(d).
- `deltaInvariant k M := Module.length k M`(4081): M이 실제 정규화 몫이라는 연결은 없다(임의 모듈).
- `padicLog`(4685): 직접 정의한 급수다. Mathlib에 대응물이 없어 다리도 없지만 정의 자체는 정확하다.
- `tau`(1879): 4-경우 공식이다. Tjurina 대수 길이와 완전히 연결된다(`quotientDimensionGoal_unconditional`, 2723). 모범 사례다.

## 6. 실질 수학 내용

진짜로 실질적인 증명:
1. Tjurina 블록(1906–2733): `k[x,y]/(x^a,y^b)`의 차원 `a·b`(`finrank_monomialQuotient` 2207, `monomialQuotientEquivIter` 2151의 다단계 몫 동형), 네 경우의 이데알 등식, 비고립 경우의 무한 길이(`length_span_f_quotient_eq_top` 2668). 가장 잘 된 부분이다.
2. 여접(cotangent)·Kähler 블록:
   - `extCotangentEquiv`(3031), `cotangentSpanSingletonEquiv`(3440): 주 아이디얼 `(f)`, f 영인자가 아님이면 `I/I² ≅ R/(f)`.
   - `cotangentComplex_repr`(3127), `compare`(3216), `cokerEquivKaehler`(3555), Fitting/unimodular 보조정리 `jacobianFullRank_of_projective_coker`(2885).
3. Tor·CRT: `card_ker_mulLeft`, `kerMulLeftEquivPiPrimePow`, `exists_avoiding_residues`, `exists_profile_avoiding`(678).
4. p-adic log: 수렴(`summable_padicLogTerm` 4722), `‖log(1+u)‖≤‖u‖`, 1·2차 근사 곱셈성.
5. 그 밖에 `abs_aPowTrace_le`(6865), `aPowTrace_eq_powerSum_complex`(1247), `traceGenFun`(4568), `ecPointCount_eq_geometric`(1163), `hensel_gate`(5000; Mathlib `hensels_lemma` 래퍼).
6. 유한 계산: `hasse_univ_F5..F13`, `ecCardF25_eq`.

비율 추정(코드 줄 4,055줄 기준, 대략치):
- 실질 수학: 약 35%(약 1,400줄). 파일 전체 8,071줄 대비로는 약 17%.
- 번들 구조체와 동어반복 인스턴스, 순환 TFAE: 약 20%. `MasterDetectors`/`GroundedDetectors`/`HypersurfaceDetectors`/`FullMasterDetectors`/`ConditionalCertificate`/`EllipticArithmeticData`의 거의 같은 재수출이 여기에 속한다.
- 재진술 래퍼: 약 20%. `PartBBundleDischarge` 5833–6266과 7360–7440이 대표적이다(대부분 기존 정리의 이름만 바꾼 한 줄 래퍼). A1/A3 모델, 예제도 포함.
- 방화벽 호출 243줄과 정의 풀기·`Iff.rfl`·`em` 정리(예: `ss_dichotomy` 891, `claim91_necessary` 2784 `:= h`, `coprime_overlap_trivial` 5166 `:= h`, `obstructionFree_iff_coprime` 1689 `Iff.rfl`, `gate_eq_jacobian` 2736 `tauto`): 약 10–15%.
- 주석: 약 24.4만 자로 파일의 대부분을 차지한다.

## 7. 수학적 정확성 및 과장

1. (Der) 검출기 과장(4절 상세): "TFAE with NO hypotheses / NO external input"(196–198, 3591–3596, 3866–3868). 실제로는 `projective : Module.Projective S Ω` 필드에 조건부다. 논문 진술 "H¹(L)=0 ⟺ smooth"는 노드에서 거짓인데 정정 목록(§Q)에 없다.
2. `ConditionalCertificate.example5` docstring 오류(6562–6565, 헤더 321): "`y² = x³ − x / 𝔽₅` (`p = 5`, `aₚ = 0`) supersingular 곡선"이라고 썼다. 같은 파일의 `ecTrace_x3mx_5 : ecTrace 5 (-1) 0 = -2`(5564), `exampleCurveX3mX_ordinary`(5589)와 모순된다. 5 ≡ 1 (mod 4)이므로 이 곡선은 ordinary다. Lean 항 자체는 그냥 `ap := 0`이라 곡선과 무관하다.
3. 층 오표기: `O(D(n)) = ℤ/n`, "`D(ab) = D(a) ∪ D(b)`"(5236). 4절과 5절 참고.
4. "BOTH external slots DISCHARGED … Theorem A's detector equivalence is consistent and realizable"(4047–4050): 지시함수 bump와 퇴화 fibre(V=0, c=0)로 채운 것이다. 논리적 무모순성만 보일 뿐 étale·motivic 내용은 0이다.
5. "ZERO trust surface over 𝔽₅/𝔽₇"(5316–5331): Hasse는 진짜로 해소됐지만 Deuring은 `geomSS := p∣aₚ`라는 정의 선택으로 사라진 것이다. 기하적 Deuring은 해소되지 않았다.
6. 헤더의 "HONEST OMISSIONS: p-adic log … out of Mathlib scope"(428–429)는 파일 안에서 `padicLog`를 정의·증명한 것과 일관되지 않는다(경미).
7. 헤더의 "785 Spt5.* results"(19행)는 검증할 수 없다(3절).
8. `gate_eq_jacobian`(2736): "Hensel ⟺ Jacobian full rank off origin"이라고 표기했지만 실제 진술은 명제 논리 항진식 `(¬a ∨ ¬b) ↔ ¬(a ∧ b)`다.
9. 칭찬할 만한 정정: C-1 min/max(5376–5394), C-2 τ=⊤(5399), C-3 `E[p]` 차수 p(5407), C-4 p=7 표 행 거부(6275–6310). 감사 정리 V.3 `tate_conclusion_is_matrix_driven`(4325)과 V.4 `isWeilPointCount_iff_trace_formula`(6402)도 스스로 공허성을 드러낸다. 다만 C-3의 Lean 내용은 정의에 의한 것이다.

## 8. 코드 품질

- 8,071줄 단일 파일이고 주석 비중이 매우 크다(헤더 430줄, 대문자 강조 docstring 남발). 섹션 순서도 뒤섞여 있다(예: `§M`이 두 번, `PartBBundleDischarge` 네임스페이스가 두 번 열림, 정의보다 늦은 "continuation" 블록).
- 같은 TFAE를 6–7개 구조체로 반복 재수출하고, B1–B9 래퍼 수십 개가 기존 정리를 다른 이름으로 복제한다.
- 증명 자체는 대체로 깔끔하다. 무거운 `simp` 남용이 적고 heartbeat 상향이 0건이다.
- 업스트림(Mathlib PR) 가치가 있는 후보:
  - `cotangentSpanSingletonEquiv`/`extCotangentEquiv`: 영인자가 아닌 f의 주 아이디얼 conormal이 rank 1 자유.
  - 초곡면 `cokerEquivKaehler`와 Jacobian 판정(`jacobianFullRank_iff_formallySmooth_uncond`, Ω 사영성 가정 아래).
  - `jacobianFullRank_of_projective_coker`(unimodular row).
  - `Tjurina.finrank_monomialQuotient`(`dim k[x,y]/(x^a,y^b) = ab`), `length_adjoinRoot_monic_pos_eq_top_of_linearIndependent`.
  - `exists_avoiding_residues`.
  - p-adic log 노름 부등식(Mathlib에 이미 유사물이 있는지는 확인하지 않았다).

## 9. 컴파일 위험

- `build-logs/`, `evidence/`, `build-evidence/` 어디에도 Spt5의 컴파일 결과 로그는 없다. `FA_QYM_13FILES_15CHECK_PIPELINE_CONTRACT_20260814.md`의 95행에 13개 필수 파일 목록으로만 등장한다. 따라서 컴파일 여부는 미확인이다.
- 위험 요소:
  - 커널 `decide` 비용: `hasse_univ_F13`, `hasse_univ_F11`, `frobenius_table_*`, `benchmark_table`, `ecCardF25_eq`, `profile_p7_*`. 파일 주석(6716–6717)은 𝔽₄₉에서 4분을 넘겼다고 직접 밝히며 그 경계 아래만 남겼다고 말한다.
  - 최신 Mathlib API 의존: `Algebra.Generators.naive`/`ker_naive`, `Extension.Cotangent.val_smul`, `Generators.H1Cotangent.equiv`, `Module.Basis.finTwoProd`, `Ideal.quotientEquivAlg`, `RingCat.hom_ext`/`ofHom`, `IsUltrametricDist.norm_tsum_le`. 핀 고정 Mathlib(2026-08-03)과 같은 시기에 작성된 것으로 보여 위험은 중간 정도다.
- 방화벽 elab은 v4.33 API(`collectAxioms`, `env.constants.map₂`)와 맞는다.

## 10. 점수 (1–10)

| 항목 | 점수 | 근거 |
|---|---|---|
| 형식적 건전성 | 8 | sorry·axiom·native_decide가 없고 방화벽이 실제로 강제된다. 컴파일 로그 부재와 무거운 `decide`로 감점 |
| 조건부 인증의 정직성(비순환성) | 4 | 많은 곳을 정직하게 표기했지만(V.3/V.4 감사, "CONDITIONAL" 라벨), 핵심 Thm A의 "UNCONDITIONAL"이 Ω 사영성 필드를 숨기고, 순환 번들과 퇴화 "grounded" 증인을 "DISCHARGED"로 홍보하며, example5 docstring이 틀렸다 |
| 수학적 실질성 | 6 | Tjurina 길이, conormal/Kähler 동형, p-adic log, Weil 전 거듭제곱 경계는 진짜다. 논문 고유의 깊은 내용(Deuring, Weil, étale, motivic, transfer)은 전부 외부화·퇴화 |
| 정의 충실도 | 5 | Weierstrass·H1Cotangent·FormallySmooth·length·SimpleGraph는 진짜. etalePTorsion·IsSupersingular·F_EC층·"구조층 ℤ/n"은 프록시이거나 오표기 |
| 코드 품질·유지보수성 | 4 | 8k줄 단일 파일, 과도한 주석, 대량 중복 래퍼. 개별 증명은 깔끔하고 업스트림 후보가 있다 |
| 종합 | 5.5 | 진짜 가치 있는 대수기하 조각이 있지만, 헤더와 docstring의 "UNCONDITIONAL / ZERO trust" 수사가 실제 내용을 크게 웃돈다 |

---

## 커버리지 로그

모든 행을 원본 `.lean`에서 순차로 읽었다. 건너뛴 구간은 없다.
- 1–450 (헤더, import)
- 450–1149 (§A EC, CRT, aSeq, Deuring, étale 모델)
- 1150–1849 (점 개수, Zeta/Weil, Vieta, FrobeniusEndoData, Hasse, Tor, CRT, residualFibre)
- 1850–2649 (Model/tau, Tjurina 블록 전반)
- 2650–3449 (Tjurina 완결, §G, §H 여접, Fitting, H1 비교, Extension 여접, HypersurfacePresentation, smoothLocus)
- 3450–4249 (cotangentSpanSingletonEquiv, conormal 동형, MasterDetectors, Grounded/Hypersurface/FullMasterDetectors, FibreCombinatorics, δ, graphBetti1, Tate)
- 4250–4799 (Tate 번들, defect complex, L-factor, traceGenFun, AB-linearization, padicLog)
- 4800–5299 (log 2차, A4ABBridge, Hensel, §8, principal open, 층/CRT, four-layer limit)
- 5300–5799 (trust 목록, frontier 목록, Corrections, EllipticArithmeticData, 𝔽₅–𝔽₁₃ 인스턴스, A5 표)
- 5800–6299 (PartBBundleDischarge B1–B9; 래퍼가 대부분이라 시그니처와 본문을 대조하며 읽음)
- 6300–6799 (C-4, II.2, 𝔽₂₅, V.4, ConditionalCertificate, Examples, §R 기저변환, §V2)
- 6800–7299 (r=2 패밀리, §RH, A5 계속, §Site, §Front, A1Coverage, A2Genus 전반)
- 7300–7749 (A2Genus 완결, PartB 계속, A3Transfer)
- 7750–8071 (방화벽 elab 두 개와 `#assert_only_safe_axioms` 243줄; 호출 목록은 이름만 훑어봄)

보조 확인:
- `scan/Spt5.code.lean` grep: set_option, macro, syntax, Inhabited, default가 0건이고 `decide` 48건.
- `decls_cls.json` 집계.
- 핀 고정 Lean v4.33.0-rc1 소스에서 `Environment.constants`와 `Name.isInternal` 의미를 확인.
- build-logs와 evidence에서 Spt5 검색.
