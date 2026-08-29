# Central-neutral-perimeter-law-lower-bound

This Lean 4 project proves a center-neutral gluelump perimeter-law lower bound
for lattice Yang--Mills theory.  It is the standalone downstream companion to
[`strong-coupling-lattice-yang-mills`](https://github.com/rn9801/strong-coupling-lattice-yang-mills).

The package has exactly one direct Lake dependency: the unchanged `main`
branch of that repository. Mathlib and the established lattice, gauge,
Wilson, and strong-coupling foundations arrive transitively through it.

The 28 additive prerequisite modules developed with the gluelump proof live
in this repository under `GluelumpPerimeterLaw.Upstream.*`: 19 extend existing
upstream modules, and nine supply new reflection/limit modules. Their module
paths are downstream-owned, while their declarations intentionally remain in
the existing `YangMills.*` namespaces. No corresponding commit or branch is
required in the Strong-Coupling repository.

## Main results in mathematical form

### Lattice, gauge group, and representations

Let $d\in\mathbb N$, let $E_d^+$ be the positively oriented nearest-neighbor
edges of $\mathbb Z^d$, and define the configuration space

```math
  \Omega_{d,G}:=G^{E_d^+}.
```

Here $G$ is a compact Hausdorff second-countable topological group equipped
with a compatible Borel structure and a chosen normalized bi-invariant Haar
probability $\lambda_G$.

**Haar full-support lemma.** For every open set $U\subseteq G$,

```math
  U\neq\varnothing \quad\Longrightarrow\quad \lambda_G(U)>0.
```

Thus positivity on nonempty open sets is a theorem for the Haar probability
in this setting, not an additional hypothesis in the headline theorems.

Let

```math
  \sigma:G\longrightarrow U(n),
  \qquad
  \rho:G\longrightarrow U(r),
  \qquad n,r\ge 1,
```

be continuous unitary representations. The Wilson plaquette potential
associated to $\sigma$ is

```math
  \Phi_\sigma(g)
  :=\operatorname{Re}\!\left(\frac{1}{n}\operatorname{Tr}\sigma(g)\right).
```

**Definition (center neutrality).** The representation $\rho$ is
center-neutral if

```math
  \operatorname{CenterNeutral}(\rho)
  \quad:\Longleftrightarrow\quad
  \forall z\in Z(G),\ \rho(z)=I_r.
```

Define the conjugation span of $\sigma$ by

```math
  \mathcal C_\sigma
  :=\operatorname{span}_{\mathbb C}\{\sigma(g):g\in G\}
  \subseteq M_n(\mathbb C),
  \qquad
  g\cdot X:=\sigma(g)X\sigma(g)^{-1}.
```

**Screening theorem.** If $\sigma$ is injective and $\rho$ is
center-neutral, then

```math
  \exists m\in\mathbb N\ \exists T:
  \mathcal C_\sigma^{\otimes m}\longrightarrow\mathbb C^r,
  \qquad
  T\neq 0,
```

where $T$ is complex-linear and $G$-equivariant, and $G$ acts on
$\mathbb C^r$ through $\rho$.

### Rectangular Wilson observables

For $x_0\in\mathbb Z^d$, coordinate directions $a,b$, and
$R,T\in\mathbb N$, let

```math
  C(x_0;a,b;R,T)
  :=(+a)^R(+b)^T(-a)^R(-b)^T.
```

When $a\neq b$ and $R,T>0$, this is a coordinate rectangle of perimeter

```math
  P(R,T):=2(R+T).
```

For $A\in\Omega_{d,G}$, define

```math
  W_\rho(C;A)
  :=\frac{1}{r}\operatorname{Tr}
    \rho\!\left(\operatorname{Hol}_A(C)\right).
```

For a probability measure $\mu$ on $\Omega_{d,G}$, set

```math
  \mathcal W^{\mathbb C}_{\mu,\rho}(x_0;a,b;R,T)
  :=\int_{\Omega_{d,G}}W_\rho(C(x_0;a,b;R,T);A)\,d\mu(A),
```

and

```math
  \mathcal W^{\mathbb R}_{\mu,\rho}(x_0;a,b;R,T)
  :=\operatorname{Re}
    \mathcal W^{\mathbb C}_{\mu,\rho}(x_0;a,b;R,T).
```

### Completed free-boundary limits

A local observable is a continuous function
$F:\Omega_{d,G}\to\mathbb C$ depending on finitely many edge coordinates.
For a real plaquette potential $\Phi$, coupling $\beta\in\mathbb R$,
direction $\tau$, and $N\in\mathbb N$, let
$\nu_{\tau,N}^{\Phi,\beta}$ be the completed link-symmetric free-boundary
Gibbs probability. Its site box is $[-N,N+1]$ in direction $\tau$ and
$[-N,N]$ in every transverse direction, with identity exterior
configuration.

**Definition (translation-invariant completed free-boundary limit).** Write

```math
  \operatorname{TIFBL}(\Phi,\beta;\mu)
```

if $\mu$ is a probability measure on $\Omega_{d,G}$ satisfying

```math
  \forall \tau\ \forall F\in C_{\mathrm{loc}}(\Omega_{d,G};\mathbb C),
  \qquad
  \lim_{N\to\infty}
    \int F\,d\nu_{\tau,N}^{\Phi,\beta}
  =\int F\,d\mu,
```

and

```math
  \forall v\in\mathbb Z^d,
  \qquad
  (\theta_v)_*\mu=\mu,
```

where $\theta_v$ is lattice translation by $v$. The limit is taken along
the entire sequence for every $\tau$, with the same limiting measure
$\mu$.

### Theorem 1 (completed free-boundary perimeter law)

Assume $d\ge 3$, $\sigma$ is injective, and
$\operatorname{CenterNeutral}(\rho)$. Then

```math
  \forall\beta\in\mathbb R,\quad
  \beta>0\Longrightarrow
  \exists c\in\mathbb R,\quad c>0,
```

such that, for every probability measure $\mu$,

```math
  \operatorname{TIFBL}(\Phi_\sigma,\beta;\mu)
  \Longrightarrow
  \forall x_0,a,b,R,T,
```

```math
  a\neq b\ \wedge\ R>0\ \wedge\ T>0
  \Longrightarrow
  \left[
    \mathcal W^{\mathbb C}_{\mu,\rho}(x_0;a,b;R,T)
    =
    \bigl(\mathcal W^{\mathbb R}_{\mu,\rho}
      (x_0;a,b;R,T):\mathbb C\bigr)
  \right]
```

and

```math
  \exp\!\bigl(-c\,P(R,T)\bigr)
  \le
  \mathcal W^{\mathbb R}_{\mu,\rho}(x_0;a,b;R,T).
```

### Theorem 2 (centered strong-coupling state)

Let

```math
  R_{\mathrm{sc}}
  :=\operatorname{latticeStrongCouplingRadius}
      \bigl(d,\operatorname{bound}(\Phi_\sigma)\bigr).
```

Assume $d\ge 3$, $\sigma$ is injective, and
$\operatorname{CenterNeutral}(\rho)$. For every $\beta>0$, there exists
$c>0$ such that, for every radius certificate
$h_\beta:|\beta|<R_{\mathrm{sc}}$, the cluster-constructed centered
probability

```math
  \mu_{\beta,h_\beta}^{\mathrm{cent}}
  :=
  \operatorname{centeredInfiniteVolumeProbability}
    \bigl(\eta_N\equiv\mathbf 1,\Phi_\sigma,\beta,h_\beta\bigr)
```

satisfies, for every $x_0$, every $a\neq b$, and every $R,T>0$,

```math
  \mathcal W^{\mathbb C}_{\mu_{\beta,h_\beta}^{\mathrm{cent}},\rho}
    (x_0;a,b;R,T)
  =
  \bigl(
    \mathcal W^{\mathbb R}_{\mu_{\beta,h_\beta}^{\mathrm{cent}},\rho}
      (x_0;a,b;R,T):\mathbb C
  \bigr)
```

and

```math
  \exp\!\bigl(-c\,P(R,T)\bigr)
  \le
  \mathcal W^{\mathbb R}_{\mu_{\beta,h_\beta}^{\mathrm{cent}},\rho}
    (x_0;a,b;R,T).
```

### Model-neutral reflection data

Let $\vartheta$ be a site, link, diagonal, or antidiagonal lattice
reflection and let $\mathcal A_\vartheta^+$ be its positive-half algebra of
local observables. For link reflections, restrict
$\mathcal A_\vartheta^+$ to gauge-invariant observables. Define

```math
  \langle F,H\rangle_{\vartheta,\mu}
  :=\int_{\Omega_{d,G}}
    \overline{F(\vartheta A)}\,H(A)\,d\mu(A).
```

**Definition (reflection-positive state).**
$\operatorname{RPS}(\mu)$ means that $\mu$ is invariant under every
lattice translation and every coordinate reflection through the origin, and
that at every affine site and link cut, and every diagonal and antidiagonal
cut with distinct axes,

```math
  \operatorname{Im}\langle F,F\rangle_{\vartheta,\mu}=0,
  \qquad
  \operatorname{Re}\langle F,F\rangle_{\vartheta,\mu}\ge 0,
```

and

```math
  |\langle F,H\rangle_{\vartheta,\mu}|^2
  \le
  \operatorname{Re}\langle F,F\rangle_{\vartheta,\mu}\,
  \operatorname{Re}\langle H,H\rangle_{\vartheta,\mu}
```

for all $F,H\in\mathcal A_\vartheta^+$. For diagonal and antidiagonal cuts
with distinct axes, it additionally requires

```math
  \overline{\langle H,F\rangle_{\vartheta,\mu}}
  =
  \langle F,H\rangle_{\vartheta,\mu}.
```

Fix $d\ge 3$, a tensor degree $m$, and an intertwiner

```math
  T:\mathcal C_\sigma^{\otimes m}\longrightarrow\mathbb C^r.
```

For $\ell,s\in\mathbb N$, let $X_\ell$, of physical length $2\ell+1$,
and $X_{\ell,s}^{\mathrm{mix}}$, of mixed physical length $\ell+s+1$, be
the canonical origin-based, link-centered screened-line observables
determined by $(d,\sigma,\rho,T)$. Define
$\operatorname{LineLink}(\mu;d,\sigma,\rho,T)$ by

```math
  \forall\ell,\qquad
  \operatorname{Im}\mathbb E_\mu[X_\ell]=0,
  \qquad
  \operatorname{Re}\mathbb E_\mu[X_\ell]\ge 0,
```

and

```math
  \forall\ell,s,\qquad
  |\mathbb E_\mu[X_{\ell,s}^{\mathrm{mix}}]|^2
  \le
  \operatorname{Re}\mathbb E_\mu[X_\ell]\,
  \operatorname{Re}\mathbb E_\mu[X_s].
```

Let $a_*$ be the canonical arm axis, $b_*$ the canonical first transverse
axis, and, for $u,v,t\in\mathbb N$, let $Y_{u,v,t}$ be the canonical
link-closed coordinate-cap observable in the $(a_*,b_*)$-plane. Define
$\operatorname{RectLink}(\mu;\rho;a_*,b_*)$ by

```math
  \forall u,t,\qquad
  \operatorname{Im}\mathbb E_\mu[Y_{u,u,t}]=0,
  \qquad
  \operatorname{Re}\mathbb E_\mu[Y_{u,u,t}]\ge 0,
```

and

```math
  \forall u,v,t,\qquad
  |\mathbb E_\mu[Y_{u,v,t}]|^2
  \le
  \operatorname{Re}\mathbb E_\mu[Y_{u,u,t}]\,
  \operatorname{Re}\mathbb E_\mu[Y_{v,v,t}].
```

Finally, define $\operatorname{SwapInv}(\mu,\rho)$ by

```math
  \mathcal W^{\mathbb C}_{\mu,\rho}
    \bigl(0;\pi(a),\pi(b);R,T\bigr)
  =
  \mathcal W^{\mathbb C}_{\mu,\rho}(0;a,b;R,T)
```

for every transposition $\pi$ of two coordinate labels and all
$a,b,R,T$.

Let $\mathcal O^{\mathrm{straight}}_{T,k}$ be the canonical direct
screened-line observable of physical length $k$, based at the origin in
the arm direction, and define

```math
  L_k(\mu;d,\sigma,\rho,T)
  :=
  \operatorname{Re}\int_{\Omega_{d,G}}
    \mathcal O^{\mathrm{straight}}_{T,k}(A)\,d\mu(A).
```

For $k=1$, this is the direct reflected one-link gluelump expectation.

### Theorem 3 (model-neutral propagation from one link)

Fix $d\ge 3$, a probability measure $\mu$ on $\Omega_{d,G}$,
representations $\sigma,\rho$, a tensor degree $m$, an intertwiner
$T:\mathcal C_\sigma^{\otimes m}\to\mathbb C^r$, and $q\in\mathbb R$.
Assume

```math
  \operatorname{RPS}(\mu),\qquad
  \operatorname{LineLink}(\mu;d,\sigma,\rho,T),\qquad
  \operatorname{RectLink}(\mu;\rho;a_*,b_*),\qquad
  \operatorname{SwapInv}(\mu,\rho),
```

and

```math
  0<q\le 1,
  \qquad
  q\le L_1(\mu;d,\sigma,\rho,T).
```

Then there exists $c>0$ such that, for every $x_0$, every $a\neq b$,
and every $R,S\in\mathbb N_{>0}$,

```math
  \mathcal W^{\mathbb C}_{\mu,\rho}(x_0;a,b;R,S)
  =
  \bigl(
    \mathcal W^{\mathbb R}_{\mu,\rho}(x_0;a,b;R,S):\mathbb C
  \bigr)
```

and

```math
  \exp\!\bigl(-c\,P(R,S)\bigr)
  \le
  \mathcal W^{\mathbb R}_{\mu,\rho}(x_0;a,b;R,S).
```

## Exact Lean statements and definitions

All three results below are exported by the package root:

```lean
import GluelumpPerimeterLaw

#check YangMills.Gluelump.InfiniteVolume.centerNeutralInfiniteVolumePerimeterLaw
#check YangMills.Gluelump.InfiniteVolume.centeredInfiniteVolume_centerNeutralPerimeterLaw
#check YangMills.Gluelump.Propagation.conjSpanPerimeterLaw_of_positiveOneLink
```

### Main theorem for completed free-boundary limits

[Statement](GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean) ·
[Proof](GluelumpPerimeterLaw/InfiniteVolumePerimeterLaw.lean)

The main proof theorem is:

```lean
theorem centerNeutralInfiniteVolumePerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) :
    CenterNeutralInfiniteVolumePerimeterLaw (d := d) sigma rho
```

Ignoring only the ambient compact-group and Haar typeclass binder list, the
proposition in its conclusion is defined by the following Lean code:

```lean
def CenterNeutralInfiniteVolumePerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r) : Prop :=
  3 ≤ d →
  Function.Injective sigma.ρ →
  CenterNeutral (asRepresentation rho) →
  ∀ beta : ℝ, 0 < beta →
    ∃ rate : ℝ, 0 < rate ∧
      ∀ mu : ProbabilityMeasure (Configuration d G),
        IsTranslationInvariantFreeBoundaryLimit
            sigma.wilsonPotential beta mu →
          ∀ (x0 : Site d) (a b : Fin d) (R T : ℕ),
            a ≠ b → 0 < R → 0 < T →
              complexRectangleWilsonExpectation mu rho x0 a b R T =
                  (rectangleWilsonExpectation mu rho x0 a b R T : ℂ) ∧
                Real.exp (-rate * (2 * (R + T) : ℕ)) ≤
                  rectangleWilsonExpectation mu rho x0 a b R T
```

#### Key definitions in the main statement

##### Center neutrality

[Source](GluelumpPerimeterLaw/RepresentationTheory/CenterNeutral.lean)

```lean
/-- A representation is center-neutral when every central group element acts
as the identity. -/
def CenterNeutral (rho : Representation k G V) : Prop :=
  ∀ z : G, z ∈ Subgroup.center G → rho z = LinearMap.id
```

Thus `CenterNeutral rho` says that every element of the center of `G` acts
as the identity on every vector. It does **not** say that `rho` is the trivial
representation: noncentral elements may act nontrivially. The definition
itself does not require irreducibility, and none of the three headline
theorems assumes that `rho` is irreducible.

##### Translation-invariant completed free-boundary limit

[Source](GluelumpPerimeterLaw/Upstream/StrongCoupling/FreeBoundaryInfiniteVolume.lean)

```lean
structure IsTranslationInvariantFreeBoundaryLimit
    (Φ : RealPlaquettePotential G) (β : ℝ)
    (μ : ProbabilityMeasure (Configuration d G)) : Prop where
  localLimit : ∀ (τ : Fin d) (F : LocalObservable d G),
    Tendsto (fun n ↦ localExpectation
      (linkSymmetricGibbsSequence Φ β τ n) F) atTop
      (nhds (localExpectation μ F))
  translationInvariant : ∀ v : Site d,
    Measure.map (LocalObservable.translateConfiguration (G := G) v)
        (μ : Measure (Configuration d G)) =
      (μ : Measure (Configuration d G))
```

Here:

- `LocalObservable d G` is a continuous complex observable depending on only
  finitely many lattice edges.
- `localExpectation μ F` is the integral `∫ A, F A ∂μ`.
- `linkSymmetricGibbsSequence Φ β τ n` is the completed free-boundary
  Gibbs probability adapted to reflection in the link plane
  `x_τ = 1/2`. Its underlying box is `[-n,n+1]` in direction `τ` and
  `[-n,n]` in every transverse direction; configurations are extended by the
  identity outside the completed finite specification.
- `localLimit` requires the **entire** sequence, for every orientation `τ`
  and every local observable `F`, to converge to expectations in the same
  probability `μ`. The current definition does not use subsequences.
- `translationInvariant` says that pushing `μ` forward by any integer
  lattice translation leaves it unchanged.

This is convergence tested against every local continuous observable, not a
total-variation convergence assertion. The main theorem is conditional on a
supplied `μ` and a proof of this structure; the definition does not assert
globally that such a probability exists. The strong-coupling corollary below
supplies one.

##### Rectangle observable and expectation notation

[Source](GluelumpPerimeterLaw/InfiniteVolumePerimeterLawStatement.lean)

```lean
def rectangleWilsonObservable {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : LocalObservable d G :=
  rho.wilsonLoop (Path.rectangleBoundary x0 a b R T)

def complexRectangleWilsonExpectation {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : ℂ :=
  localExpectation mu (rectangleWilsonObservable rho x0 a b R T)

def rectangleWilsonExpectation {d r : ℕ} {G : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    [SecondCountableTopology G] [GaugeHaarProbability G]
    (mu : ProbabilityMeasure (Configuration d G))
    (rho : ContinuousUnitaryRepData G r)
    (x0 : Site d) (a b : Fin d) (R T : ℕ) : ℝ :=
  (complexRectangleWilsonExpectation mu rho x0 a b R T).re
```

Pointwise, `rectangleWilsonObservable` is the normalized character

```lean
(r : ℂ)⁻¹ * Matrix.trace
  (rho.ρ (holonomy A (Path.rectangleBoundary x0 a b R T)))
```

The boundary travels `R` bonds in direction `+a`, then `T` in direction
`+b`, followed by `R` in direction `-a` and `T` in direction `-b`; its
perimeter is `2 * (R + T)`. The definitions themselves allow coincident axes
and zero side lengths, while the theorem assumes distinct axes and positive
side lengths.

The complex expectation is not definitionally real;
`rectangleWilsonExpectation` is only its real part. The first conclusion of
the headline theorem proves that the complex expectation equals this real
number coerced back to `ℂ`, after which the lower bound is genuinely a bound
on the expectation itself.

Thus, in dimension at least three, a faithful action representation `sigma`
and a center-neutral Wilson representation `rho` give a uniform
perimeter-law lower bound at every positive coupling, conditional on the
stated thermodynamic limit.

For every basepoint, every ordered pair of distinct coordinate axes, and all
positive side lengths, the theorem proves both

- that the Wilson-loop expectation is real; and
- that it is at least `exp (-rate * perimeter)`.

The rate depends only on `d`, `sigma`, `rho`, and `beta`. Its quantifier comes
before `mu` and all rectangle data, so it is uniform over the limiting
probability, basepoint, axes, and side lengths. The theorem itself has no
small-coupling restriction; away from strong coupling it is conditional on
the existence of a probability satisfying the full-limit hypothesis.

### Concrete strong-coupling corollary

[Source](GluelumpPerimeterLaw/StrongCouplingPerimeterLaw.lean)

```lean
theorem centeredInfiniteVolume_centerNeutralPerimeterLaw
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (hd : 3 ≤ d)
    (hsigma : Function.Injective sigma.ρ)
    (hcenter : CenterNeutral (asRepresentation rho))
    (beta : ℝ) (hbetaPos : 0 < beta) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ hbeta : ‖(beta : ℂ)‖ <
          latticeStrongCouplingRadius d sigma.wilsonPotential.bound,
        ∀ (x₀ : Site d) (a b : Fin d) (R T : ℕ),
          a ≠ b → 0 < R → 0 < T →
            complexRectangleWilsonExpectation
                (centeredInfiniteVolumeProbability
                  (fun _ ↦ (1 : Configuration d G))
                  sigma.wilsonPotential beta hbeta)
                rho x₀ a b R T =
                (rectangleWilsonExpectation
                  (centeredInfiniteVolumeProbability
                    (fun _ ↦ (1 : Configuration d G))
                    sigma.wilsonPotential beta hbeta)
                  rho x₀ a b R T : ℂ) ∧
              Real.exp (-rate * (2 * (R + T) : ℕ)) ≤
                rectangleWilsonExpectation
                  (centeredInfiniteVolumeProbability
                    (fun _ ↦ (1 : Configuration d G))
                    sigma.wilsonPotential beta hbeta)
                  rho x₀ a b R T
```

The strong-coupling infrastructure proves that the cluster-constructed
centered Wilson probability satisfies the completed-box limit hypothesis.
This supplies an unconditional application of the main theorem whenever
`beta > 0` lies inside the cluster-expansion radius. The same rate is chosen
before the radius witness and before all rectangle data.

### Model-neutral propagation theorem

[Source](GluelumpPerimeterLaw/Propagation/ConjSpanPerimeterLaw.lean)

```lean
theorem conjSpanPerimeterLaw_of_positiveOneLink
    (mu : ProbabilityMeasure (Configuration d G))
    (hstate : ReflectionPositiveState mu)
    (hd : 3 ≤ d)
    (sigma : ContinuousUnitaryRepData G n)
    (rho : ContinuousUnitaryRepData G r)
    (T : IntertwiningMap (tensorPower (conjSpanRep sigma) m)
      (asRepresentation rho))
    (hlineLink : ConjSpanLinkReflectionData mu hd sigma rho T
      (0 : Site d) (conjSpanCornerZeroArm hd))
    (hrectangleLink : CanonicalRectangleLinkReflectionData mu rho
      (Geometry.armAxis_ne_transverseAxis₁ hd))
    (hswap : RectangleAxisSwapInvariant mu rho)
    {q : ℝ} (hq : 0 < q) (hqOne : q ≤ 1)
    (hqseed : q ≤ conjSpanPhysicalStraightExpectation
      mu hd sigma rho T (0 : Site d) (conjSpanCornerZeroArm hd) 1) :
    ∃ rate : ℝ, 0 < rate ∧
      ∀ (x₀ : Site d) (a b : Fin d) (R S : ℕ),
        a ≠ b → 0 < R → 0 < S →
          (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
              ∂(mu : Measure (Configuration d G))) =
              ((∫ A, rho.wilsonLoop
                (Path.rectangleBoundary x₀ a b R S) A
                  ∂(mu : Measure (Configuration d G))).re : ℂ) ∧
            Real.exp (-rate * ((2 * (R + S) : ℕ) : ℝ)) ≤
              (∫ A, rho.wilsonLoop (Path.rectangleBoundary x₀ a b R S) A
                ∂(mu : Measure (Configuration d G))).re
```

This is the reusable mathematical engine. A positive direct one-link
gluelump seed, a reflection-positive state, the two gauge-fixed crossing-link
interfaces, and coordinate-swap invariance imply the real exponential
rectangle bound. This theorem contains no finite-volume exhaustion, cluster
expansion, thermodynamic-limit assumption, or strong-coupling radius.

The project-specific interfaces in this theorem mean:

- [`ReflectionPositiveState`](GluelumpPerimeterLaw/Upstream/Gauge/ReflectionPositiveState.lean)
  bundles translation and coordinate-reflection invariance together with
  positivity and Cauchy--Schwarz for site, link, diagonal, and antidiagonal
  reflection pairings at every affine cut, plus Hermitian symmetry for the
  diagonal and antidiagonal pairings. Its ordinary link fields apply to
  gauge-invariant positive-half observables; crossing gauge-covariant
  gluelump endpoints require the separate link interfaces below.
- [`ConjSpanLinkReflectionData`](GluelumpPerimeterLaw/Propagation/ConjSpanPhysicalStraightExpectation.lean)
  supplies reality, nonnegativity, and mixed Cauchy--Schwarz for the odd,
  link-centered gluelump lines. In the completed-box construction these
  inequalities are obtained by crossing-link gauge fixing.
- [`CanonicalRectangleLinkReflectionData`](GluelumpPerimeterLaw/Propagation/CanonicalRectangleExpectation.lean)
  supplies the corresponding half-integer-cut positivity and
  Cauchy--Schwarz statements for balanced and mixed coordinate caps.
- [`RectangleAxisSwapInvariant`](GluelumpPerimeterLaw/Propagation/CanonicalRectangleExpectation.lean)
  says that transposing any two coordinate labels leaves every origin-based
  rectangular Wilson-loop integral unchanged.
- `conjSpanPhysicalStraightExpectation ... length` is the real expectation
  of the direct screened line with exactly `length` arm bonds. At length one
  it is exactly the reflected one-link seed whose positive lower bound is
  assumed in `hqseed`.

Together with the action data, nonnegative coupling, and geometric
assumptions, the completed-box limit hypothesis supplies all of these
interfaces in the main proof; they are explicit assumptions only in the
model-neutral propagation theorem.

### Screening construction

The screening map is constructed directly as
`(ConjSpan sigma)^⊗m → rho`. Accordingly, the normalized Higgs-like endpoint
is `rho`-valued and transforms by the ordinary Wilson representation action;
the active construction does not pass through the algebraic dual of `rho`.

## Proof integrity

All repository-owned Lean sources are free of `sorry`, `admit`, `sorryAx`,
project-defined `axiom` or `constant` declarations, and `unsafe`
declarations. The five `noncomputable opaque` definitions each have an
explicit `:= by` body which Lean kernel-checks; opacity controls reduction
and does not introduce an axiom or proof gap.

A compiled `Lean.collectAxioms` audit of every project declaration found no
nonstandard axiom dependency. In particular, the complete axiom footprint of
each of the three headline theorems is exactly

- `propext`;
- `Classical.choice`; and
- `Quot.sound`.

These are Lean's standard foundational principles, not axioms introduced by
this project. The regression suite records the headline footprints and
rejects nonstandard axioms on the neutral critical path; CI also rejects proof
placeholders, source-level `axiom` declarations, and unsafe declarations.

This does not mean that the mathematical statements have no hypotheses. The
compact-group, representation, dimension, positive-coupling or seed, and
limit hypotheses are explicit in the theorem signatures above. Full support
of normalized Haar measure is derived from those ambient compact-group and
Haar-probability hypotheses. Some reusable auxiliary theorems likewise take
explicit data or proposition interfaces as arguments. None is installed
globally or hidden as an unproved internal assumption. See
[the mathematical assumptions](docs/MATHEMATICAL_ASSUMPTIONS.md) for the
complete accounting.

## Build

```bash
lake update
lake build
lake build GluelumpPerimeterLawTests
```

Import the public API with:

```lean
import GluelumpPerimeterLaw
```

Module paths use the `GluelumpPerimeterLaw.*` prefix so Lake can distinguish
this package from the upstream `YangMills` library.  Existing declaration
namespaces remain `YangMills.Gluelump.*`.

## Upstream compatibility overlay

`GluelumpPerimeterLaw/Upstream` is an additive compatibility overlay on the
current upstream `main`; it does not replace or modify files in the dependency
checkout. When upstream `main` eventually acquires one of these declarations,
the corresponding downstream extension must be removed (and its imports
retargeted) in the same compatibility update, otherwise Lean will correctly
report a duplicate declaration. Scheduled CI updates the dependency to the
latest `main` so that transition is detected immediately.

The GitHub repository is private for now.

See [the roadmap](docs/ROADMAP.md), [the mathematical assumptions](docs/MATHEMATICAL_ASSUMPTIONS.md),
and [the status ledger](STATUS.md).

## License and provenance

The project is released under Apache-2.0. The initial standalone source and
its 28 compatibility modules were extracted from the gluelump development in
`strong-coupling-lattice-yang-mills`; individual Lean files retain their
original copyright and contributor notices. See [NOTICE](NOTICE).
