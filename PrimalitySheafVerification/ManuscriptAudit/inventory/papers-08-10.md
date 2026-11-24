# 8–10편 수학적 주장 목록

페이지는 첨부 overleaf_bundle (Copy).pdf의 첫 장을 1로 세는 **물리 PDF 페이지**다. 정리, 보조정리, 가정의 번호는 원문의 표기를 따른다. 같은 주장이 여러 절에 등장하면 서로 다른 가정이나 정규화가 있는 곳에 함께 적었다.

각 행의 주장은 원문의 내용을 요약한다. 검증 메모는 원문과 기존 Lean 소스의 대조 결과다. 반례가 적용되는 범위와 추가로 필요한 가정을 기록했다. 수치 표에는 원문에 기재된 결과를 옮겼다. 이 목록 자체는 Lean 커널 실행 결과를 포함하지 않는다.

## 8편 — Entropy–Growth and Sheaf Stability for Mock/Partial Theta and Jacobi Objects

본문은 302–395쪽에 있다. 299–301쪽은 표제와 목차이며, 참고문헌은 395–397쪽이다.

| PDF 쪽 | 원문 표기 | 원문 주장과 가정 | 검증 메모 |
|---|---|---|---|
| 302 | §1.2(C2)–(C5), §1.3, Entropy-growth theorem | 고정한 무게 ½ Rademacher 전개에서 log abs(a(n)) = α√n − ½ log n + β + o(1). 첫 모듈러스 항이 α를 정하며, 국소화와 p진 완비화에 대해 α가 불변이라고 한다. | 정확한 계수 전개, 주항의 비소멸, 나머지와 주항의 상대 크기, 수송 후 주항의 비교가 필요하다. |
| 302 | §1.3, Degeneracy matching 및 Cardy constant and stability | 판별식과 호환하는 d(n)=a(n) 또는 고정 선형결합에도 같은 α가 적용되고, K를 2K로 바꾸는 오차는 O(exp(−γ√n))이라고 한다. c_eff=6α²/π²이며 gcd(M,p^k)=1이면 α와 c_eff가 변하지 않는다고 한다. | 고정 선형결합에서 주항 상쇄를 배제해야 한다. 이 페이지의 c_eff 식과 386–391쪽의 정규화가 다르다. |
| 303–304 | §2(i)–(viii) | 모듈러 변환과 cusp 성장, 무게 k Laplacian과 ξ의 인수분해, 조화 Maass 분해와 그림자, f의 Eichler 완비화, 상·하반평면의 mock/partial 표현을 인용한다. Hk 아래 AB 로그를 mod p^k로 선형화하고 이차 나머지의 p진 차수가 ≥2k라고 한다. | ξ의 켤레 및 Laplacian 부호를 고정해야 한다. p진 전개는 로그의 정의역과 정량적 차수를 따로 확인해야 한다. |
| 304, 306–307 | §2(vii), D1의 SPT reduction, S5 | ker(ℤ→ℤ/M×ℤ/p^k)=(M)∩(p^k)=(lcm). Tor₁^ℤ(ℤ/M,ℤ/p^k)≅ℤ/gcd이며 두께는 min(v_p(M),k). 국소화와 완비화에서 양립한다고 한다. | 겹침의 정수 차이에 관한 조건과 Tor의 소멸을 구분한다. p가 M을 나누면 양의 k를 바꿔도 이 Tor를 없앨 수 없다. |
| 305–306 | D1, S4, (*) | u₀=τ/2, v₀=(τ+1)/2, z₀=−½의 극 회피와 특수화된 μ 급수. 양방향 n에 동일한 기하 전개를 적용해 음의 주부분과 n=−1−m의 ridge를 얻고, 처음 q 지수를 −5/4,−13/4,−25/4로 제시한다. S4는 D×2D 계수 행렬을 만들고 최소노름 해를 계산한다. | 기하급수 전개는 수렴이 서로 다른 두 범위에서 별도로 필요하다. 최종 Laurent 지수에는 θ 분모와 q 위상도 영향을 준다. |
| 306–309 | T1, (3.1)–(3.3), Remark 3.1 | u와 v를 같은 mτ+r만큼 이동하면 z₀가 보존된다. E(n,ℓ,m)의 m에 관한 아핀식을 사용하여 각 선택 행이 자기 열에서만 가장 낮고, ±1 대각 소행렬로 rank D를 얻는다고 한다. | 기울기가 하나인 아핀 함수는 내부 열에서 양쪽 열보다 엄밀히 작을 수 없다. 다른 (n,ℓ)에서 오는 충돌도 검토해야 한다. |
| 309–311 | T2, Table 1 | D=11, J=22, N=80, ℓ₀=50에서 지수 중복이 없고 A=[I∣−I]라고 한다. b=e₁의 최소노름 해와 수치 잔차를 보고하며, cusp 0의 행도 쌓을 수 있다고 한다. | Table 1의 지수 자체에 중복이 있다. 선언된 행렬에 대한 선형대수와 실제 Laurent 계수 행렬의 식별은 별도다. |
| 311 | T3, Proposition 1 | 같은 z₀의 유한 블록에 bμ=μ+(i/2)R(z₀)를 적용하면 bF=F⁺+(i/2)S R(z₀), S=Σc_j다. | 고정 블록 완비화로부터 나오는 유한합 항등식이다. 정확한 완비화 상수는 적용하는 정규화를 따라야 한다. |
| 311–312 | Proposition 2, Corollary 1 | 공통 그림자 g_z₀에 대해 ξ₁/₂bF=κSg_z₀인 비영 κ를 주장한다. S=0이면 F⁻=0, ξbF=0이며 약한 정칙 모듈러 형식이라고 한다. | 표준 ξ는 반선형이므로 복소 계수에는 켤레가 필요하다. ξ=0에서 약한 정칙 모듈러성을 얻으려면 변환 법칙과 cusp 조건도 필요하다. |
| 312–313 | T4, Lemma 1 | S 변환을 한 각 μ 블록은 원문의 √(−iτ)exp(πiz₀²/τ) 인자와 고정 Mordell 보정 h(z₀;τ)/(2i)로 표현된다고 한다. | 지수의 부호, 인자의 위치, 실제 τ-의존 블록에서 u/τ,v/τ의 재특수화를 맞춰야 한다. |
| 313 | Proposition 3, Corollary 2 | 완비화 후 bF의 S-slash가 bF와 같고 cusp 0에서 완만한 성장. ∞에서 얻은 A와 cusp 0의 A를 쌓고 각 cusp의 주부분을 지정해 풀 수 있다고 한다. | 정확한 multiplier와 Mordell 상쇄가 필요하다. 각 블록 행렬의 rank만으로 결합 시스템의 전사성은 따르지 않는다. |
| 313–315 | T5 Proposition, (3.4)–(3.5) | T2에서 합성한 G의 외부 계수가 G(q⁻¹)=2ψ(q)−S(q)를 만족한다고 한다. S를 2ψ(q)−f(q⁻¹)로 두고 f의 수치 항등식을 검사한다. | f를 사용한 정의가 임의 합성 G=f라는 사실을 보장하지 않는다. 동일한 가지, 수렴영역, 주항과 성장 조건이 필요하다. |
| 315–317 | D3, (3.6)–(3.9) | D=6, J=12 예제의 구체 행렬과 c, 잔차 약 9.742×10⁻¹⁶, S=1을 보고한다. 한 개의 R항과 S배의 공통 Mordell 보정으로 cusp 0의 성장과 그림자를 제어한다고 한다. | 315쪽은 개별 완비화에 −½를 쓰고 합에는 +½를 쓴다. ξ의 반선형성과 수치 잔차를 구분한다. |
| 317–318 | D4.Eq, D4.Tor, D4.Sync | 각 cusp의 주부분 벡터에 mod M 및 mod p^k 조건을 부과하고 lcm 모듈러 조건으로 합친다. z₀ 고정에 따라 S가 cusp별로 동일하게 이동한다고 한다. | 같은 목표의 두 정수 합동조건은 lcm으로 합쳐진다. 실제 cusp 수송에 따른 계수 및 그림자의 동일성은 별도다. |
| 319 | D5.1–2, (3.10)–(3.14), Lemma 2 | N=∏q^{k(q)}에 대해 Tor의 소인수별 직접합, IC=Σ min(v_q(M),k(q))log q와 CRT 조건을 제시한다. Hk 아래 모든 소수의 로그 선형화가 단일 CRT 조건과 동치라고 한다. | Tor에는 min이 들어간다. 식 (3.13)의 교집합에는 lcm의 max 지수와 M에만 나타나는 소수도 들어간다. |
| 320–321 | D5.3–4, §2.3 | 주부분과 그림자를 고정하면 외부 급수가 CRT 자료까지 결정된다고 한다. M=12, N=3·2^k의 Tor는 ℤ/3 ⊕ ℤ/2^{min(2,k)}. D=6의 데이터·κ=1·S=1·잔차 허용치를 기록한다. | 예제 Tor 계산은 정수 문제다. 정수 합동이 해석적 외부 급수의 유일성으로 이어지려면 대응 정리가 필요하다. |
| 321–324 | §3.1(A)–(F), §3.2, §4.1(1)–(6) | ξ 인수분해, f의 β-kernel 완비화, 동일 z₀ µ의 이중급수, f/ψ/S의 안팎 항등식과 상·하반평면 통합, CRT/Tor를 반복한다. D=3의 블록과 수치 주부분·보정 비교를 제시한다. | bilateral 전개의 부호, f와 q^{-1/24}f의 선택, ψ의 여러 정의 및 q의 거듭제곱을 행별로 고정해야 한다. |
| 325–327 | Theorem A / Theorem 3.2(i)–(iii), ND2–ND5 | 임의 복소 c_j에 대해 정해진 그림자·무게 ½ Γ(2) 조화성, ∞와 0의 주부분 실현 및 고정 그림자 아래 유일성을 주장한다. 완비화 계수 α=½와 i/2를 제시한다. 수치 검사는 블록 합, 커널, T/S 잔차 및 두 S(q) 구현을 비교한다. | 원문의 개별 −½와 합산 +½는 양립하지 않는다. 유일성에는 주부분과 그림자가 모두 0인 관련 정칙 공간의 소멸이 필요하다. |
| 328–331 | §4.2(A)–(E), §4.3 ND3–ND5 | F⁺의 변환 결함을 g*가 복구하고 ξg*가 무게 3/2 unary theta라고 한다. T/S 비율과 수치 잔차, Euler 곱·pentagonal 구현 비교를 제시한다. | T 오차와 S 오차가 다르며, 331쪽의 실제 BF pairing 잔차는 0.00648–0.08865다. 두 보정 구현의 일치와 전체 항등식 검사는 구분한다. |
| 331–333 | §5.1, Proposition A.1 | ξ₁/₂bF=κ θ_{χ−12,1}, θ=Σ_{n∈ℤ}χ_{−12}(n)n q^{n²/24}. κ는 첫 비영 계수로 정해지며, n≡1 mod 6의 급수와 비영 상수배로 같다고 한다. | 양방향과 양의 지표만의 급수, 문자와 지표 조건을 각각 비교해야 한다. κ의 최소제곱 적합은 해석적 계수 비교가 아니다. |
| 334–336 | §5.2.1–5, C.1.1 | 조화 Maass 분해, canonical 예제와 Eichler 커널, Rogers 항등식, 두 반평면의 표현, 등화자·Tor를 정리한다. | 각 인용은 해당 정규화와 변환군에 맞는 별도 입력이다. |
| 337 | Lemma 3 | 직사각형 격자에서 χ_T≈1 및 χ_S≈exp(−πi/6)을 적합한다. | 수치 적합에 관한 주장이다. Γ(2)의 cusp 주기를 정하는 T²와 T를 구분해야 한다. |
| 338 | Proposition C.1, §C.1.2(D) | 이번에는 θ=Σ_{n≥1}χ_{−12}(n)nq^{n²/24}로 놓아 ξbF=κθ를 주장하고 κ_LS 및 Petersson형 이산 지표를 계산한다. | A.1의 양방향 합과 다르다. 유한차분 적합을 정확한 도함수 값으로 대체하려면 오차 분석이 필요하다. |
| 339–344 | §6.2, (B), D, worked example | Zwegers R의 표현과 Mordell 상쇄, S/T 및 Jacobi 법칙, µ 대칭, 동시 정수 타원 이동, f와 ψ 및 보정 S의 예제와 수치 구현을 제시한다. | 340쪽의 동시 정수 이동 인자는 정확한 재인덱싱과 어긋난다. 343쪽은 수치 큰 인자의 상쇄·절단에 관한 주의다. |
| 345–347 | §8.1.0–4 | q-급수 정의와 완비화, 모듈러 의미를 요약하고 multiplier/타원 법칙의 수치 검사와 필요한 후속 조건을 기록한다. | 보고된 근사치와 정확한 항등식의 확인 상태를 구분한다. |
| 348 | §8.2.1, G.0.1–2 | 극 계수·Kloosterman-type kernel·I₁/₂로 Rademacher 계수식을 제시하고 multiplier에 쓰는 행렬의 행렬식이 1이라는 조건을 준다. | 표시한 행렬의 행렬식은 적힌 합동만으로 항상 1이 되지 않는다. |
| 349–350 | G.0.3–7, G.1 D1 | K≈√n, K→2K, c=1 주항과 Cauchy 계수 추출을 비교한다. 세 cusp의 slash와 θ 분모를 둔 µ 급수에서 음의 계수를 출력한다. | 350쪽의 m²/2 지수는 305쪽의 m/2와 다르다. 여기 적힌 θ는 평가점 (1+τ)/2에서 정수 지표 짝짓기로 소멸한다. |
| 351–355 | G.1.1–8 | 세 cusp의 극 성분과 결정된 multiplier를 입력으로, a priori Rademacher 꼬리, K/2K 안정성과 외부 Cauchy 일치를 주장한다. | 절댓값을 씌운 개별 모듈러스 상한이 임계 지수인 경우에는 합의 수렴과 상쇄를 별도로 증명해야 한다. |
| 355–358 | §8.3.1–2 | unimodal 제약 모델, 유한 모드 값, 대칭·성장에 관한 진단과 표를 제시한다. | 유한 계산 및 실제 무한 q-급수와의 식별이 각각 필요하다. |
| 359–361 | §9.1.1–2, (I.1)–(I.5) | Θ_ker=y^αΣ_{n∈ℤ}ψ(n)exp(πin²τ), β=1, α<−½. T/S 위상이 완비화와 맞고 비영 커널로 쓰인다고 한다. | 적힌 mod 4 홀수 문자를 쓰는 양방향 합은 n과 −n의 상쇄로 0이다. |
| 362 | Lemma 4, Proposition I.1 | y→0에서 θ=O(y^{1/2})를 제시하고 O(y^{α−1/2})의 적분이 α<−½에서 수렴한다고 한다. | 절댓값 항 수 추정은 O(y^{−1/2})와 관련된다. ∫₀^{y₀}y^p dy는 p>−1에서 수렴하며, 그 영역은 ∞ cusp의 위쪽이 아니다. |
| 363–365 | §9.1.3, J.1, Proposition J.1 | β=1, C∞=lim_{β↓1}(4π)^{1−β}Γ(β−1)⁻¹(2π)^−½로 두면 L(F)=C∞Σc(n)b(n)가 절대수렴하며 표준 Rankin–Selberg 정규화와 맞고 잔여 Γ(0,4πn) 항이 없다고 한다. | 표시한 극한은 0이다. β=1에서 0부터 시작하는 y⁻¹exp(−4πny) 적분에는 정칙화가 필요하다. |
| 366 | Lemmas 5–6, (K.3) | unfolding으로 L(F)=C∞Σ_{n≥1}c(n)b(n), theta 계수 b(n)가 문자 지지를 갖고 이차 twist를 만든다고 한다. | x 적분이 n=m을 선택하려면 켤레 또는 반대 부호가 필요하다. 실제 커널이 주는 지지와 인수는 따로 계산해야 한다. |
| 367 | Lemma 7, Proposition K.1 | 실제 반정수 multiplier의 Weil형 상한 Cε c^{1/2+ε}(m,n,c)^{1/2}. A(n)=C′ n^{α₀}L(½,f⊗χ_D(n))∏_{p∣ND(n)}L_p(n), 주항과 국소 Euler 인자. | Kloosterman 상한만으로 실제 f-isotypic 성분 선택과 국소 인자를 얻을 수 없다. |
| 368 | Lemma 8, Theorem K.2 | root number −1이면 A(n)=0. +1이면 위 중심값 식을 얻는다고 한다. K.2는 Lemma 7의 Weil 상한을 가정한다. | L 함수의 functional equation에서의 소멸과 A(n)과의 실제 period/계수 동일시가 각각 필요하다. |
| 369–371 | §§9.1.5–6, I.2.1 | K/2K, 커널 범위, T/S 위상 검사를 수치로 제시하고 p진 겹침에 필요한 산술 입력을 정리한다. | 표의 수치는 입력 함수·절단·수치 오차를 고정한 재현 대상으로 본다. |
| 372–373 | Lemma 9, (I.1), Remarks I.1–2 | q^{-α}로 지수 이동을 제거하고 유한 유리 계수의 분모를 정수 d로 제거한다. d 또는 p^{k−1}d₀를 곱해 a_p∈ℤ_p이고 a_p≡a mod p^k라 한다. | 적분성은 분모를 제거하면 따른다. 합동은 v_p((d−1)a)≥k 같은 별도 조건이 필요하다. |
| 374–375 | I.2.3, Proposition I.3 | 유한 principal-open cover, 정규화와 Hk 아래 cusp 수송의 값들이 (M)∩(p^k) modulo에서 겹침에 일치하고 전역 단면이 된다고 한다. | 실제 mod M 호환성과 정확한 전역 단면의 형식이 필요하다. |
| 376–379 | I.2.4, Proposition I.4 | 유한 데이터에 일치하는 Mahler 급수와 j>N인 c_j∈p^kℤ_p, 겹침과 전역 단면을 주장한다. | 유한 삼각계는 유일하게 풀고 높은 계수를 0으로 연장할 수 있다. 그 연장이 실제 무한 계수열과 일치하는지는 별도다. |
| 379–381 | I.2.5, Proposition I.5 | Hk와 균일 Rademacher/Kloosterman 꼬리에서 N₀를 정해 초기 일치, 이후 cusp 계수의 p^k 가분성, 동일한 전역 단면을 얻는다고 한다. | 입력 꼬리의 p진 가분성만으로 Mahler 차분 꼬리의 가분성은 보장되지 않는다. δ₀의 Mahler 계수는 (−1)^j다. |
| 381–382 | I.2.6, Item 5 | 공통 M,p^k와 절단 N₀를 정하고 Mahler 보간이 같은 전역 p진 면이라고 선언한다. M=50,p=5,k=2 예제로 검증한다. | mod 25 조건만으로 교집합 (50) 소속은 확인할 수 없다. 실제 정수 차이를 확인해야 한다. |
| 383–386 | §9.3 Q1–Q5, Items A–B, B.1–5 | c=1 항으로 계수·엔트로피를 설명하고 Jacobi 판별식 슬라이스와 물리 degeneracy d(n)의 계수 식별을 제안한다. | 모형에서 택한 채널, 실제 계수 동일시, 선형결합에서 비소멸을 각각 확인해야 한다. |
| 386–387 | Theorem I.6, (I.3)–(I.6), Remark I.7 | K₀=⌊κ√n⌋에서 비영 c=1의 크기 M(n)에 대해 abs(R_{>K₀})/M(n)≤Cn^B exp(−γ√n). K와 2K의 차이도 꼬리로 제어한다고 한다. | 증명이 사용하는 Σ_{c>K₀}c^ε는 발산한다. 주항 상대 꼬리와 절대 꼬리는 별개다. I₁/₂ 공식의 상수도 확인해야 한다. |
| 388–390 | Items D–E, D.1–2, E.1–2 | log abs(a(n))을 √n, log n, 상수로 OLS하고 c_eff=6(α/2)²/π²와 표준오차를 산출한다. | 이 정규화의 미분은 3α/π²다. 389쪽에는 이 값의 절반이 인쇄되어 있다. |
| 390–391 | Theorem I.8(i)–(ii), Remark I.9 | gcd(M,p^k)=1이면 모든 면/cusp에서 α,c_eff가 같고 임의 M에서 기울기 차이는 tail+O(SE들의 합)이며 극한 불일치가 겹침/Tor를 통해 인수분해된다고 한다. | CRT는 일치하는 잔여류의 결합을 보장한다. 해석적 c=1 항과 OLS 민감도는 이에 추가해 확인해야 한다. |
| 392–395 | J.1–2, Remarks J.1–2, K.1(C1–C5), K.2–4 | 재현 절차가 완비화·수송·꼬리·겹침·기울기를 인증한다고 요약한다. K.1은 절대 꼬리의 지수 감쇠, Cardy 수치, 퇴화도 식별, gcd=1에서의 (α,β) 불변을 진술한다. | K.1의 꼬리와 c_eff 식은 앞 절의 상대 꼬리·정규화와 다르다. K.2의 균일 꼬리·이차항·p진 범위·모티브 확장은 원문이 열어 둔 문제다. |

## 9편 — Global Poincaré Matching and Kloosterman-Compatible Test Kernels for Half-Integral Weight Mock–Theta Gauge Objects

본문은 398–456쪽에 있다. 457–458쪽은 참고문헌이다.

| PDF 쪽 | 원문 표기 | 원문 주장과 가정 | 검증 메모 |
|---|---|---|---|
| 398–400 | Abstract, §§1.2–1.5, Item 1 | 한 tent 계열의 비음성, 지지와 Fourier 비음성을 이용해 스펙트럼과 Kloosterman 쪽에서 함께 쓴다. Θ=y^α θ의 T/S 위상과 β=1, α<−½에서의 적분가능성을 8편으로부터 가져온다. | 대수적 위상, 불변 밀도, cusp 수렴 및 실제 Kuznetsov 허용 함수의 조건은 각각 확인해야 한다. |
| 401–402 | Definitions 1–2, Remark 1.1 | Γ(2), ν와 인쇄된 R₁/₂,L₁/₂에서 비가중 hyperbolic L²와 두 미분을 사용해 compact support smooth core를 완비화한다. V=H¹, V′=H⁻¹이며 단면은 역 무게 ½ covariance를 만족한다. | core의 함수값과 완비화에서의 a.e. 단면을 구분한다. 미분으로 옮겨가는 무게와 불변 내적을 정확히 지정해야 한다. |
| 402 | Definition 3 | 각 cusp ∞,0,1의 scaling과 폭 2, F_Y=F∩{모든 y_κ≤Y}의 상대콤팩트성, 조각별 매끄러운 경계 및 소진을 제시한다. | 구체적인 다각형, scaling, 경계 모서리와 면 접합에서 검증할 수 있다. “임의” 기본영역의 경계가 자동으로 그런 것은 아니다. |
| 402–403 | Lemma 1.1, Proposition 1, (1.1)–(1.5) | 약한 식 ∆u+Vu=f를 compact support test v와 짝지으며, v의 지지를 담는 절단에서 적분한다. dual norm의 단위구/단위구면 비율과 Hölder를 제시하고 고정 F_Y 위의 모든 v로 같은 sup를 취한다. | 테스트별 절단과 고정 절단의 전체 sup는 다르다. ∆u의 분포값과 적분대표를 맞춰야 한다. |
| 404–405 | Step 4, (1.6)–(1.10), Remark 1.3 | 두 인수분해와 수반으로 Green 항등식을 얻고, horocycle 경계항에 Y^{−1/2} trace 상한을 적용해 전역 식을 얻는다고 한다. | 두 인수분해는 f=y에서 실패하는 기존 Lean 반례가 있다. 두 식을 평균하면 ½가 필요하다. 경계 소멸에는 trace 노름의 균일 성장 제어가 필요하다. |
| 405 | Lax–Milgram Steps 2–3, (1.11)–(1.16), Remark 1.4 | B가 연속이며 충분한 λ를 더한 B_λ는 coercive다. 유일한 u와 노름 추정을 얻고 같은 f를 쓰면서 원래 식의 해라고 한다. | Lax–Milgram의 결론은 B_λ(u,v)=f(v)다. 원래 식에 옮기면 f−λu의 항이 생기며 별도 가역성 또는 보정이 필요하다. |
| 406–409 | Quoted Ingredients Q2.A–F | ν에 대한 Selberg cusp/residual/Eisenstein, 연속 문턱 ¼, scattering meromorphic 및 unitarity와 functional equation, Maaß–Selberg, Kuznetsov와 Weil/Kohnen–Andersen을 인용한다. | 실제 승수와 표준화·정의역에 대해 필요한 입력 목록이다. 인용되는 식과 아래의 정규화가 일치하는지 확인해야 한다. |
| 409–412 | §1.6.1–5, (1.18)–(1.24), Lemma 1.2 | 스펙트럼 직교 분해와 Parseval, 무게를 바꾼 미분의 norm identity, 양의 이산 λ_min에서 Eis 직교 u에 대해 ‖u‖≤C_GP(‖Ru‖+‖Lu‖). | 해당 multiplier에서 실제 분해가 필요하다. 0 고유공간, 수반의 무게, 미분과 고유급수 극한을 정당화해야 한다. |
| 412–414 | Lemma 1.3, (1.26)–(1.30) | Weil형 상한과 Bessel의 작은 x에서 x^{1/2}, 큰 x에서 x^{−1/2} 상한으로 K_ν(m,n)≤Cε(1+mn)^{1/4+ε}. | ∑c^{−1+ε}는 발산한다. (mn)^{1/4}를 m,n에 독립인 상수로 흡수할 수 없다. |
| 415–417 | Definition 4, Proposition 2, (1.32)–(1.33) | H_mass는 m≥m₀에서 E_Φ(m,m)≥ε_mass. Global Poincaré와 Kloosterman 다항 상한 및 H_mass로 λ₀≥¼+ε_mass를 주장한다. | 고정 양의 하한과 증가하는 상한은 양립한다. 무한한 계수 활동성과 지배율을 보여야 하고 λ<¼에는 실수 t 표현이 없다. |
| 417–418 | Lemma 2.1, (2.1) | 이산 부분에서 양의 λ_min과 인쇄된 R/L 에너지 등식을 통해 λ_min^{-1/2}의 Poincaré 상수를 얻는다. | 인쇄된 μ-무게의 λ_min 및 3/16 주장과 R/L 항등식을 실제로 검증해야 한다. 최소 비영 고유값을 사용할 때 0 고유모드의 제거가 필요하다. |
| 418–419 | Lemma 2.2, (2.2)–(2.4) | 작은 x에서 유계인 Bessel과 Weil 상한으로 Lemma 1.3의 같은 m,n 상한을 얻고 ε를 작게 선택한다. | ∑c^{−1/2+ε}도 발산한다. gcd 인자는 m,n에 독립이지 않다. |
| 420 | Lemma 3.1, Definition 5 | β=1, α<−½인 bF·Θ·y^β가 절대적분 가능하고, Re s가 큰 영역에서 Eisenstein E(·,s)를 더 곱한 R(s)도 수렴한다고 한다. | 8편의 수렴 증명 문제가 이어진다. E를 곱한 적분에는 E의 cusp 성장이 포함된 조건이 필요하다. |
| 421–422 | Definitions 6–7, Propositions 3–4, Corollaries 3.1–3.2 | dμ_cont=(4π)⁻¹tr(S′S⁻¹)dt로 E_Φ를 정의한다. unitarity와 compact support, 비음 Fourier로부터 실수 양의 밀도와 m에 균일한 질량 하한을 주장한다. | unitarity와 reciprocal 식만으로 양의 로그 도함수가 따르지 않는 스칼라 반례가 있다. 양의 밀도와 커널에도 계수의 균일 하한이 필요하다. Corollary 3.1은 명시적으로 H_mass를 사용한다. |
| 423 | Lemma 3.2, Remark 3.3 | Φ_T=1_{[−T/2,T/2]}∗1_{[−T/2,T/2]}는 비음, [−T,T] 지지, Fourier 비음이다. | 실제 실수 convolution으로 계산하고 Fourier 정규화에 맞춘다. |
| 424–425 | Lemmas 3.3–3.4, Proposition 5, B.2.4(A1)–(A3) | Φ_T(t₀)=T−abs(t₀), 넓이 T², abs(t)≥abs(t₀)의 넓이 (T−abs(t₀))², T≥2abs(t₀)+1이면 Φ_T(t₀)≥T/2. 기하 transform은 C T²와 x^{−1/2} 봉투로 제어한다고 한다. | tent 적분과 실제 반정수 Kuznetsov transform 검증은 별도다. |
| 425–426 | Lemmas 3.5–3.7, (3.1)–(3.3) | Re s>1의 R_m(s)를 F_m(t), s(1−s)+t² 및 scattering 로그 도함수로 전개한다. 전개 절대수렴·Fubini와 mass functional의 동일시·비음성을 주장한다. | 실제 E,S,F_m, 정규화, 극 및 분모, 교환 정당화와 밀도 부호를 확인해야 한다. |
| 427–428 | Lemma 3.8, Propositions 6–7, Corollary 3.3 | Mock I nondegeneracy에서 모든 큰 m의 지지구간 unweighted L² 활동을 하한으로 잡는다. 이로부터 E_Φ≥ε를 얻고 discrete 기여가 비음일 때 S_Φ≥E_Φ≥ε라고 한다. | tent는 지지 끝점에서 0이다. 밀도 및 tent의 양의 내부 하한과 그곳의 활동성을 공급해야 한다. Proposition 7은 제목과 달리 본문에서 활동성을 가정한다. |
| 428–429 | S1, (3.7)–(3.12) | 실제 Kuznetsov 대각 식과 t₀ 실수 및 tent localization에서 S_Φ(m,m)≥c₁ abs(ρ₀(m))²+ε를 얻는다. | 올바른 대각/켤레, test transform과 H_mass가 전제다. |
| 429–431 | S2, (3.13)–(3.18), Proposition 8 | Fourier–Whittaker와 Parseval로 전역 L²를 양의 계수 가중합으로 표현한다. cutoff Poincaré와 dyadic 평균으로 무한한 큰 계수를 뽑아 S_Φ≥c₁c₀g+ε를 주장한다. | 전역 quotient가 전체 높이의 단일 strip은 아니다. 양의 계수합은 단일 지표에 집중할 수 있다. 무한 활동 또는 각 블록의 하한이 필요하다. |
| 431–432 | S3, Proposition 9 | 실제 대각 Kloosterman 식과 Bessel/Weil을 합쳐 L_up=Cε(1+m²)^{1/4+ε}. λ₀<¼+ε이면 무한한 admissible m에서 L_low>L_up라고 한다. | 비교에 필요한 지수 차이나 양의 성장률이 앞 단계에서 공급되지 않는다. 실제 상한은 수렴 검증도 필요하다. |
| 433–434 | Item 3 §§3.1–3.3, (3.20)–(3.26) | F=O_X·F⁺에 ∂̄+A를 두어 F⁺ 평행. 곡률 ∂̄A를 cΘΘdτ∧dτ̄와 동일시하고 양의 shadow 에너지와 평행 단면의 미분 에너지가 경계 소멸 후 같다고 한다. | 순수 (0,1) connection의 제곱은 (0,2) 값을 가지며 복소 1차원에서 0이다. F⁺가 평행하면 좌변의 에너지도 0이다. |
| 435–436 | §4.1–3, (4.1)–(4.9), Proposition 10 | torsion pole이 있는 meromorphic Jacobi φ의 finite/polar 분해. ℓ=0 finite coefficient로 inside f, polar의 Appell–Lerch로 outside 2ψ−S, bG로 glue와 변환을 얻는다고 한다. | 고정 φ의 실제 Laurent·theta coefficient와 채택한 mock prototype의 동일시가 필요하다. |
| 437–439 | Item 5, (4.10)–(4.27), Proposition 11 | Rademacher 절대 꼬리 가정과 성장 abs(a(n))≤Cn^B exp(A₀√n), horocycle Parseval로 F⁺_{≤N}의 균일 H¹와 precompactness를 주장한다. | Y_N=C/√N의 핵심 n/√N≥√n은 n≤N에서 역방향이다. 고정 양의 높이의 수렴과 전역 H¹ control은 범위가 다르다. |
| 440–441 | Definitions 8–9, (4.28)–(4.29), Remarks 4.3–4.4 | quotient의 전역 q 및 radius로 Laplacian을 공액하고 unitary equivalent라 한다. radius별 해의 국소상수층과 H_q에 의한 canonical 평행수송 및 flatness. | 실제 Γ(2)에서 q와 radius 모두 내려가지 않는다. 국소 chart를 정해도 unitary map, operator domain과 미분방정식이 추가로 필요하다. |
| 442–443 | §§4.5.1–3, §5.1, (4.30)–(4.32) | shadow로 정한 S, outside G(q⁻¹), Eichler 보정 F⁻가 주는 조화 Maass 완비화. radius의 fibre를 ker(H_q−λ)의 제한으로 해석한다. | 정확한 Eichler 적분 경로·분기와 ξ 및 공변성, fibre의 정의역·수송이 각각 필요하다. |
| 444 | Definition 10, Proposition 12, (5.1) | 안쪽 f, canonical S, ∞ 근처 G(q⁻¹), 공통 annulus의 정칙 Ψ가 있고 G(q⁻¹)=2Ψ−S 및 유일성. | 실제 공통 영역과 Ψ,S의 확인이 필요하다. 그 영역에서의 동일성은 주어진 해석적 연장과 일치로부터 얻을 수 있다. |
| 445 | Proposition 13(i)–(iii) | 각 cusp a에 γ∈Γ(2)로 ∞를 a로 보내 수송한 f_a,S_a,G_a와 항등식, H_q가 정하는 cusp 성장 및 stalk를 얻는다고 한다. | 0과 1은 ∞와 다른 Γ(2) 궤도다. ambient SL₂(ℤ)의 scaling 수정은 가능하며, 그 수정이 나머지 해석적 주장까지 해결하지는 않는다. |
| 446 | Theorem 5.1(i)–(iii) | 같은 bF와 S*를 써서 inside, outside 및 공통 annulus를 glue한다. bounded radial difference가 0이며 스펙트럼이 cusp 성장을 제어한다고 한다. | H 위에는 abs(q)>1이 없다. radial 구간에서 유계인 비영 정칙 함수가 존재한다. |
| 447–448 | Definition 11, Proposition 14, Remark 6.1 | L_q가 국소상수이고 고유한 flat connection이 H_q의 evolution을 평행수송으로 실현한다고 한다. local expression은 d/dlog r+A_q. | 기존 source의 관계는 generator를 바꾸어도 같은 해를 가질 수 있다. 구체 ODE와 well-posedness가 필요하다. |
| 449 | Definitions 12–14, Remark 6.2 | A_q=L_q⊗M_mock, 국소 단면을 pair로 설명. D_q=∇⊗id+id⊗d_q 및 두 boundary map의 equalizer E_q를 구성. | 텐서 원소와 한 쌍을 구분한다. connection의 정의역·스칼라 Leibniz와 실제 boundary maps가 필요하다. |
| 450 | Proposition 15, Remark 6.3 | balanced field를 소수별 spectral profile로 보내고 등화자 및 Tor와 호환하는 canonical functor Sh(E_q)→Sh(P). | 범주, base, 사상과 Tor 사이 자연 변환의 실제 정의가 필요하다. |
| 450–451 | Definition 15, Lemma 6.1, Proposition 16 | deck covariance (6.2)의 smooth 1-form presheaf, restriction stability 및 strict overlap sheaf를 얻는다. | 실제 covariance의 제한과 매끄러운 형식의 strict gluing을 확인하는 구조적 주장이다. |
| 452–453 | Definitions 16–17, Propositions 17–18, (6.4)–(6.11) | ∇=d+A 및 F=dA+A∧A. local gluing·restriction 호환, admissible g의 affine action 아래 F^g=g⁻¹Fg. | typed ordinary wedge DGA와 admissible action을 고정한다. twist를 적용해도 동일하게 성립하는지는 별도다. |
| 454 | Definition 18, Proposition 19, Remark 6.7 | flat locus F=0. L=‖F‖²+M+R, M,R 비음, zero-energy flat witness, 형식 EL 아래, 주어진 flat global minimizer에서 M=R=0. | 비음인 블록과 0인 비교 원소로 얻는 조건부 주장이다. minimizer 존재 또는 spectral gap은 별도다. |
| 455 | Proposition 20, (6.13)–(6.14) | open cover에서 strict compatible local fields는 product restrictions의 equalizer이고 유일하게 glue한다. | 적절한 sheaf에 대한 엄밀한 구조적 주장이다. special q interface의 존재는 별도다. |
| 455–456 | Proposition 21(i)–(iii), Remark 6.9 | Z→Z/M×Z/p^k의 kernel=lcm ideal, cokernel=Z/gcd인 exact sequence와 Tor₁≅Z/gcd. | 차이 mod gcd 및 자유분해로 계산하는 산술 주장이다. 실제 gauge spectral bounds를 Tor로 보내는 사상은 별도다. |

## 10편 — Modular q–Yang–Mills on Γ(2)\ℍ

본문은 459–505쪽에 있다. 참고문헌은 505–507쪽이다.

| PDF 쪽 | 원문 표기 | 원문 주장과 가정 | 검증 메모 |
|---|---|---|---|
| 459–461 | Abstract, §1 | admissible gauge slice, split energy, modular flow와 cusp-truncated low-lying gap 기법을 제시한다. | 원문의 해석적 입력과 증명된 조건부 함의를 각 절에서 추적한다. |
| 462 | §§2.1.1–3, (2.1)–(2.3) | ν(cτ+d)^{−1/2}를 인자로 하는 pullback covariance, strict overlap 조건 및 End(E)의 wedge·matrix product를 고정한다. | ordinary quotient form과 비자명 automorphic line에 값을 갖는 형식을 구분하고 곱의 목표 무게를 지정해야 한다. |
| 463 | Definitions 2.1–2.2, Proposition 2.2, (2.4)–(2.6) | [A,B]_q=AB−qBA, ∇=d+A, F=dA+A∧A. 미분과 곱·bracket은 restriction과 strict gluing에 호환된다. | 보통 wedge DGA와 중심 q에서는 locality를 정식화할 수 있다. bracket의 입력·출력 bundle은 따로 지정해야 한다. |
| 464 | Proposition 2.3, (2.7)–(2.9) | admissible g의 affine connection action 아래 ordinary curvature가 공변이고, 두 형식을 homogeneous conjugation할 때 strong bracket도 공변이다. | affine curvature와 homogeneous bracket은 서로 다른 식이다. 이 명제는 affine bracket의 공변성을 요구하지 않는다. |
| 465 | §2.2, (2.12)–(2.16) | hyperbolic Hodge ∗를 좌표로 주고, 양의 정부호 Ad-invariant pairing으로 L²를 정의한다. 모든 admissible variation에서 cusp boundary가 사라진다고 가정한다. | 양의 Ad-invariant form은 선택된 gauge group/real form의 가정이다. GL₂(ℂ)의 전체 adjoint action에는 존재하지 않는다. (2.16)은 원문이 부과하는 조건이다. |
| 466–467 | (2.17)–(2.18), Axiom 2.3, Remark 2.4 | H¹ 및 H⁻¹, 유한에너지 cusp admissibility. σ가 algebra automorphism이고 Tr_q(XY)=Tr_q(σ_q(Y)X). 특수화 σ_q(Y)=qY를 사용한다. | abs(q)<1이면 q·id는 unital automorphism이 될 수 없다. 이 스칼라 규칙이 모든 입력을 덮으면 trace는 0이다. 양의 비퇴화 pairing에는 별도 구조가 필요하다. |
| 468 | §3.3.1–2, Axiom A3.M, (3.3)–(3.4) | continuous spectral mass에서 M_q를 만들고 M_q≥c₀‖A‖²−C₀를 가정한다. V_q를 각 cusp의 target과 추출값 차이의 제곱합으로 둔다. | mass의 비음성, 엄밀한 하한, 추출 maps의 연속성과 공변성을 각각 확인해야 한다. |
| 469 | Axioms A3.V, A3.R, A3.T, (3.5)–(3.7) | 모든 δ>0에서 abs(V)≤δ‖F‖²+Cδ, abs(R_T)≤δ‖F‖²+ε(T), ε(T)→0. 공변 입력으로부터 M,V,R의 gauge invariance 및 EL 적합성을 주장한다. | 점별 제어와 δ,T에 균일한 제어는 다르다. 입력이 equivariant일 때 값의 functional도 invariant여야 한다. |
| 470 | Proposition 3.1 | 고정 T에서 minimizing sequence는 curvature+L² energy에 유계이고 H¹ 약수렴 부분수열을 가진다. lower-order blocks는 absorbable이다. | curvature+L²에서 H¹ 제어로 가는 gauge estimate와 약한 closure가 필요하다. |
| 471 | Lemmas 3.2–3.3, (3.9)–(3.16) | 중심 q와 trace 호환 조건에서 affine A^g,B^g의 strong bracket, curvature와 leading energy가 공변 또는 불변이라고 한다. | (3.15)의 affine bracket은 유한 matrix jet 반례가 있다. (3.16)과 에너지에는 올바른 curvature law와 trace conjugacy가 필요하다. |
| 472 | Proposition 3.4, (B.M)–(B.R) | M,V,R을 admissible g에 불변으로 선택하고 leading block이 불변이면 full density/action도 불변. | 각 블록의 불변성을 입력으로 사용하는 가법성 주장이다. |
| 472–475 | §§3.7–3.9, (3.17)–(3.26), D-check | absolute/relative Coulomb, 허용 variation 및 weak pairing을 고정한다. q=.95의 격자에서 finite-difference/variation과 EL residual을 보고하고 twisted Bianchi residual을 shadow forcing으로 제안한다. | variation의 상대 차이는 약 28%이고, oscillatory 및 theta probe의 잔차가 0이 아니다. 격자 결과는 continuum Bianchi 항등식을 증명하지 않는다. |
| 475–477 | Definition 3.1, Assumptions 3.5–3.6, Remark 3.7, Assumption 3.8 | H¹ gauge-fixed class, finite energy 및 cusp admissibility. 네 블록 정의 가능, M의 c₀ 하한과 V 흡수, R은 H¹ 유계 집합에서 제어, uniform trace 상한으로 boundary 소멸. | R의 유계집합 제어는 전역 coercivity를 보장하지 않는다. trace norm의 성장과 양의 감쇠를 함께 확인한다. |
| 477–479 | Definition 4.1, Proposition 4.1, Definition 4.2 | compact G의 cusp-admissible field/variation, δF=D_Aα+E_braid, leading energy의 한 항 first variation과 경계 소멸 후 weak EL, all variations에서 criticality. | 한 항으로 합치려면 quadratic pairing 대칭이 필요하다. E_braid가 0이거나 EL 식에 따로 들어가야 한다. |
| 479–481 | §4.2.1–6, (4.1)–(4.5) | lower bound, minimizing H¹ weak subsequence와 local strong L²/L⁴, admissible weak closure, curvature 및 M,V,R의 weak l.s.c.를 통해 minimizer와 weak EL. | H¹ estimate, 비어 있지 않은 admissible set, weak closure, 블록별 l.s.c. 및 허용 방향에서의 differentiability를 검증해야 한다. |
| 481–482 | §4.3.1–3, Definition 4.3, Axiom 4.4 | inside/outside/cusp cover, abs(q)=1을 만나는 annulus에서의 strict H¹ equality와 모든 IBP boundary의 소멸. | q=exp(2πiτ)인 ℍ 내부에는 interface와 exterior가 없다. cusp 소멸은 여기서 공리로 쓰인다. |
| 482–483 | Lemma 4.2, Theorem 4.3, §4.3.6 | strict transitions로 unique global admissible H¹ section. 각 chart에 local minimizer가 있고 boundary가 죽으면 glue가 전역 최소를 이루고 전역 weak EL. | local H¹만으로 전역 integrability는 보장되지 않는다. 일반 에너지에서 strict gluing과 local minima로 global minimum은 따르지 않는 유한 반례가 있다. partition of unity는 gauge tangent를 보존해야 한다. |
| 484–486 | §4.4.1–5, (4.7)–(4.18) | A∈L∞(I;H¹)와 ∂tA∈L²(I;H⁻¹), 네 블록의 variational gradient, ∂tA+Φ(A)=0와 stationary weak criticality. 충분히 regular하다고 두고 L² 속도제곱의 소산과 interface matching을 제안한다. | 실제 gradient의 Riesz pairing과 시간 chain rule이 필요하다. H⁻¹ 속도는 H¹ 테스트와 그대로 짝지을 수 없다. |
| 487–488 | Theorem 4.4 (Theorem B), (4.19)–(4.21) | H1 sectorial elliptic L 및 locally Lipschitz H¹→H⁻¹ nonlinear term, H2 cusp persistence, H3 local/restriction 및 interface agreement. 모든 A₀에서 유일한 local H¹/L²H² solution, covariance/gluing, −‖Φ‖²_{H⁻¹} 소산과 H¹ bounded continuation을 주장한다. | H1 규모의 Lipschitz만으로 parabolic sign은 고정되지 않는다. dual Riesz lift, chain rule, 추정과 covariance의 보존도 필요하다. (4.17)은 L²를 쓰고 (4.21)은 H⁻¹을 쓴다. |
| 489 | Theorem 4.5, (4.22)–(4.28) | twisted trace, admissible projection의 self-adjointness에서 B_q의 두 변수에 관한 skew, B_q(u,v)와 v의 pairing 소멸, N_q(u)와 u의 pairing 소멸을 주장한다. | −Tr_q(UV)는 적힌 대로는 복소 쌍선형이다. twisted cyclicity와 자기수반 projection에서 full skew가 따르지 않는 matrix 반례가 있다. |
| 490 | Remark 4.6, §§4.6.3–4, Corollary 4.7 | finite Galerkin ODE 및 C^k_ij의 triple product, C^k_ij=−C^j_ik, 대각 0, nonlinear energy cancellation을 주장한다. | 시공간 flow와 모드의 정확한 pairing과 선형부 부호를 맞춰야 한다. last-two-index skew에는 보정된 skew/ad-invariance가 필요하다. |
| 491 | Assumption 4.8, Theorem 4.9, Remark 4.10 | s>½에서 B_q:H^s×H^s→H^{s−1} bounded, q에 locally uniform. dual pairing으로 abs(C^k_ij)≤‖B_q‖‖φ_i‖_{H^s}‖φ_j‖_{H^s}‖φ_k‖_{H^{1−s}}. | 결론은 정확한 pairing bound와 B_q 연속성에서 나온다. 실제 projected braided product의 추정은 가정이다. |
| 492–493 | §4.7.1–3, (4.38)–(4.41), Remarks 4.11–4.12 | Dirichlet Coulomb H_gs와 projector Π_gs, δ_q=Π_gs∇^(q), ∆_q=δ_q*δ_q로 정한다. projection은 L²/H¹ bounded이며 직접 제한과 동치라고 한다. | H¹ trace와 전체 L² closure, 미분의 목표형식, projector의 정의역, 제한에 대한 불변성이 필요하다. |
| 493–494 | Lemma 4.13 | 닫힌 비음 형식의 Friedrichs realization은 유일한 nonnegative self-adjoint ∆를 준다. H² domain 포함과 분포 δ*δ 공식을 주장한다. | concrete δ의 dense/closed graph, coercive norm equivalence와 boundary elliptic regularity가 추가로 필요하다. |
| 494 | (4.42)–(4.43), Proposition 4.14 | Hessian이 L∞, fibrewise self-adjoint이면 V가 gauge slice의 bounded self-adjoint multiplication. H=−∆+V는 self-adjoint이고 ≥−‖V‖. | V의 slice 보존이 필요하다. ∆=δ*δ≥0이면 minus sign에서 하한 주장은 일반적으로 거짓이다. |
| 495 | Proposition 4.15, §4.7.6, (4.44) | fixed finite Y에서 compact resolvent, orthonormal eigenbasis, finite multiplicities, 오름차순 λ_n→+∞. min–max form에는 +‖δa‖²를 사용한다. | −∆+V와 양의 kinetic form은 다르다. compact resolvent와 ordering 방향은 구분한다. |
| 496 | §4.8.1, Lemma 4.16 | 높이 부등식으로 만든 quotient, D_Y=H¹₀∩H_adm, projected D_q,Y의 closedness와 density, nonnegative Friedrichs form. | raw height sublevel은 Γ(2)-불변이 아니다. ambient dense core와 closed slice의 교집합이 자동 dense는 아니다. |
| 497 | Lemmas 4.17–4.18, Definition 4.5, Remark 4.19 | L∞ perturbation, lower semibounded plus form, compact embedding 및 compact resolvent와 증가 eigenbasis. m²=λ₀, δ_Y=λ₁−λ₀, δ=liminf_Y δ_Y. | 구체 compact embedding과 slice의 operator realization이 필요하다. m을 실수로 두려면 λ₀≥0, 첫 distinct gap에는 ground multiplicity 처리가 필요하다. |
| 498 | Hypotheses 4.20, 4.22, Proposition 4.23, (4.46)–(4.47) | M≥0이며 N⊥에서 M≥c_RS‖·‖², h≥αM+β‖·‖². λ₀≥β, N⊥에서 h≥(αc_RS+β)‖·‖². N이 ground에 포함되면 δ_Y≥αc_RS라고 한다. | 두 form 하한은 함께 쓸 수 있다. 상대 gap 결론은 diag(100,100.5)의 matched simple ground 반례에서 실패한다. 반복 ground이면 adjacent gap이 0일 수도 있다. |
| 499 | Hypothesis 4.24, Corollary 4.25 | admissible spaces의 일관된 소진과 inf_Y αc_RS>0에서 liminf_Y δ_Y>0. | ground-shifted gap의 실제 균일 양의 하한이 먼저 필요하다. |
| 499 | Theorem 4.26 | 모든 n≥1에서 abs(Â(n))≤C n^{−1/2}exp(α√n). Rademacher 범위의 정확한 주항 C₀ n^{−1/2}exp(α√n)과 O(n^{−1}exp(α√n)). | 실제 계수 전개와 균일한 나머지가 본체다. eventual bound는 상수를 조정해 유한 prefix까지 확장할 수 있다. |
| 500 | Definitions 4.6–4.7, Proposition 4.27, Corollary 4.28 | T0–T4의 localized family와 real t_j에서 N_Φ=ΣΦ_T(t_j). fixed Y, compact admissible q에서 uniform O(1+T), Φ≥1_{[T,T+1]}로 window density. | real t는 λ≥¼를 가정한다. 균일 q의 local Weyl remainder와 허용 family의 window 하한이 필요하다. |
| 501 | Lemma 4.29 | Φ_T로부터 얻은 Ψ_T의 large-t decay에서 t_j≥T+(log T)²인 합이 모든 A>0에서 O(T^{−A}). | decay와 window count에 T,q-균일 상수가 필요하다. 한 T에서의 compact support로는 전 가족의 꼬리를 제어하지 못한다. |
| 501–502 | Definition 4.8, Lemma 4.30, (4.48) | B1은 real L∞ μ, B2는 abs(⟨μu,u⟩)≤aQ[u]+b‖u‖², 0≤a<1. B1 operator sum self-adjoint 및 spectral enclosure, B2 KLMN closed lower semibounded form. | 실제 Hessian에서 얻은 μ와 form bound를 제공해야 한다. 두 perturbation 정리의 추상 결론을 실제 연산자와 연결해야 한다. |
| 502 | Theorem 4.31, Corollary 4.32, (4.49)–(4.50) | B1에서 각 고유값 변화≤‖μ‖, gap loss≤2‖μ‖ 및 δ/4에서 절반 유지. B2는 [(1−a)λ_n−b,(1+a)λ_n+b]와 index-uniform 제어 및 유사 gap bound를 주장한다. | B2의 올바른 오차는 λ_n에 의존한다. 인접 gap 손실에는 a(λ_n+λ_{n+1})+2b가 나타난다. |
| 503 | Corollary 4.33, §4.10.3 | B1에서 I의 corrected count는 ‖μ‖만큼 양쪽을 넓힌 I의 reference count 이하이며 역방향도 성립한다. μ를 cusp/shadow penalty의 선형화로 설명한다. | 순서·multiplicity를 유지한 고유값 오차로부터 count bound가 나온다. 실제 penalty의 선형화 식은 별도다. |
| 503–504 | Lemmas A.1–A.2, Definition A.1, Remark A.3 | H=−∆+V의 lower bounded SelfAdjoint, compact resolvent 및 증가 eigenvalues, adjacent low-lying gap을 반복한다. | 본문과 같은 kinetic sign 및 도메인 제어가 필요하다. |
| 504–505 | Hypotheses A.4, A.6, Remark A.5, Theorem A.7 | RS mass nonnegative 및 N⊥에서 c_RS, form domination αM+β. λ₀≥β 및 complement 하한, 주장된 δ_Y≥αc_RS와 δ의 liminf 하한을 합친다. | β 하한은 λ₀의 upper bound를 주지 않는다. 실제 전체 ground eigenspace의 직교 여공간에 대해 ground-shifted coercivity를 쓰는 보정이 필요하다. |

## 기존 Lean 대응 예시

- 9편 404쪽의 두 Maass 인수분해에는 높이 함수 반례가 있다. [Mock2_Advanced.lean 17748행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/Mock2_Advanced.lean#L17748)
- 9편 412–419쪽 꼬리에 쓰인 두 비교급수의 발산을 분리해 둔 Lean 선언이 있다. [Mock2_Advanced.lean 6484행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/Mock2_Advanced.lean#L6484)
- 9편 421–422쪽 산란 행렬의 unitarity만으로 양의 로그 도함수를 얻는 추론에는 스칼라 반례가 있다. [Mock2_Advanced.lean 23757행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/Mock2_Advanced.lean#L23757)
- 9편 445쪽의 Γ(2) cusp 수송에 대한 반례 및 ambient scaling 보정이 있다. [Mock2_Advanced.lean 14725행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/Mock2_Advanced.lean#L14725)
- 9편 440–448쪽의 전역 q와 radius는 실제 Γ(2) 궤도 공간으로 내려가지 않는다. [QYM.lean 30737행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/QYM.lean#L30737)
- 10편 466–467쪽의 스칼라 automorphism, 471쪽의 affine bracket, 482–483쪽의 전역 최소성 추론에 대한 Lean 반례가 있다. [QYM.lean 7629행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/QYM.lean#L7629), [7670행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/QYM.lean#L7670), [2160행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/QYM.lean#L2160)
- 10편 498쪽과 505쪽의 β 기준선 추론과 502쪽 B2의 index-uniform 오차에 대한 Lean 반례가 있다. [QYM.lean 30033행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/QYM.lean#L30033), [8124행](https://github.com/leegahuyn/FORMALIZATION-OF-MY-10-PAPERS/blob/0e026509fad2d4910f1f90b3cd7aea80f15a8902/PrimalitySheafVerification/QYM.lean#L8124)
