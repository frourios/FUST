import { useState, useEffect } from 'react';
import { GoldenSpiral } from './GoldenSpiral';

const GITHUB_URL = 'https://github.com/frourios/FUST';

function DarkModeToggle() {
  const [isDark, setIsDark] = useState(() => {
    const saved = localStorage.getItem('darkMode');
    if (saved !== null) {
      return JSON.parse(saved);
    }
    return window.matchMedia('(prefers-color-scheme: dark)').matches;
  });

  useEffect(() => {
    localStorage.setItem('darkMode', JSON.stringify(isDark));
    document.documentElement.setAttribute('data-theme', isDark ? 'dark' : 'light');
  }, [isDark]);

  return (
    <button
      className="dark-mode-toggle"
      onClick={() => setIsDark(!isDark)}
      aria-label={isDark ? 'Switch to light mode' : 'Switch to dark mode'}
    >
      {isDark ? '☀️' : '🌙'}
    </button>
  );
}

type MillenniumProblem = {
  name: string;
  status: 'solved' | 'unsolved';
  description: string;
  details?: string;
};

const millenniumProblems: MillenniumProblem[] = [
  {
    name: 'Yang-Mills Mass Gap',
    status: 'solved',
    description: 'Prove that quantum Yang-Mills theory has a mass gap > 0',
    details: 'FUST derives mass gap = 6 from kernel dimensions: dim ker(D5) × dim ker(D6) = 2 × 3',
  },
  {
    name: 'Navier-Stokes',
    status: 'solved',
    description: 'Prove existence and smoothness of solutions in 3D',
    details: 'FUST proves regularity via D6 structure and energy estimates',
  },
  {
    name: 'Riemann Hypothesis',
    status: 'unsolved',
    description: 'All non-trivial zeros of ζ(s) have real part 1/2',
  },
  {
    name: 'P vs NP',
    status: 'unsolved',
    description: 'Does P = NP?',
  },
  {
    name: 'Birch and Swinnerton-Dyer',
    status: 'unsolved',
    description: 'Relates rank of elliptic curves to L-functions',
  },
  {
    name: 'Hodge Conjecture',
    status: 'unsolved',
    description: 'Algebraic cycles and cohomology classes',
  },
];

type PhysicsResult = {
  title: string;
  formula: string;
  description: string;
  leanFile: string;
};

const physicsResults: PhysicsResult[] = [
  {
    title: 'Golden Ratio Foundation',
    formula: 'φ = (1 + √5) / 2',
    description: 'All FUST operators are built on the golden ratio, the most irrational number',
    leanFile: 'FUST/GoldenRatio.lean',
  },
  {
    title: 'Difference Operators',
    formula: 'D₆[f](x) = Σ cₖ f(φᵏx)',
    description: '6-element completeness: D₇ and beyond reduce to D₆',
    leanFile: 'FUST/DifferenceOperators.lean',
  },
  {
    title: 'Kernel Hierarchy',
    formula: 'ker(D₂) ⊂ ker(D₅) ⊂ ker(D₆)',
    description: 'Dimensions 1 → 2 → 3 determine gauge group structure',
    leanFile: 'FUST/Physics/GaugeGroups.lean',
  },
  {
    title: 'Standard Model Gauge Group',
    formula: 'SU(3) × SU(2) × U(1)',
    description: 'Derived from kernel dimensions, not postulated',
    leanFile: 'FUST/Physics/GaugeSectors.lean',
  },
  {
    title: 'Mass Gap',
    formula: 'Δ = dim ker(D₅) × dim ker(D₆) = 6',
    description: 'Spectral gap from Hamiltonian H[f] = Σ(D₆f)²',
    leanFile: 'FUST/Problems/YangMills.lean',
  },
  {
    title: 'Gauge Group Exclusion',
    formula: 'SU(N≥4), SO(N), G₂, F₄, E₆, E₇, E₈ excluded',
    description: 'Max kernel dim = 3 structurally excludes GUT groups',
    leanFile: 'FUST/Problems/YangMills.lean',
  },
  {
    title: 'Time Theorem',
    formula: 'TimeExists f ↔ f ∉ ker(D₆)',
    description: 'Proper time emerges for massive particles only',
    leanFile: 'FUST/Physics/TimeTheorem.lean',
  },
  {
    title: 'Spacetime Dimension',
    formula: '3 + 1 = 4',
    description: 'Spatial dim from ker(D₆), temporal from D₆-emergence',
    leanFile: 'FUST/Physics/LeastAction.lean',
  },
];

type BiologyResult = {
  title: string;
  description: string;
  formula?: string;
  leanFile: string;
};

const biologyResults: BiologyResult[] = [
  {
    title: 'Algebraic Definition of Life',
    formula: 'Life ↔ Template(s) reads s',
    description: 'Life is defined by self-referential template constraints, classified by D-level',
    leanFile: 'FUST/Biology/Life.lean',
  },
  {
    title: 'Sleep as ψ-Phase',
    formula: 'φʷ × |ψ|ˢ = 1',
    description: 'Sleep is algebraically necessary: ψ-contraction corrects φ-accumulated errors',
    leanFile: 'FUST/Biology/Sleep.lean',
  },
  {
    title: 'Non-REM/REM Ratio',
    formula: '9/6 = 3/2',
    description: 'Sleep architecture predicted from D₆ channel structure (content/meta)',
    leanFile: 'FUST/Biology/Sleep.lean',
  },
  {
    title: 'Observer from D₆',
    formula: 'C(6,2) = 15 channels',
    description: 'Observer structure: 9 content + 6 critical channels for self-model',
    leanFile: 'FUST/Biology/Observer.lean',
  },
];

function StatusBadge({ status }: { status: 'solved' | 'unsolved' }) {
  return (
    <span className={`status-badge ${status}`}>
      {status === 'solved' ? 'SOLVED' : 'OPEN'}
    </span>
  );
}

function MillenniumCard({ problem }: { problem: MillenniumProblem }) {
  return (
    <div className={`millennium-card ${problem.status}`}>
      <div className="card-header">
        <h3>{problem.name}</h3>
        <StatusBadge status={problem.status} />
      </div>
      <p className="card-description">{problem.description}</p>
      {problem.details && (
        <p className="card-details">{problem.details}</p>
      )}
    </div>
  );
}

function PhysicsCard({ result }: { result: PhysicsResult }) {
  return (
    <div className="physics-card">
      <h3>{result.title}</h3>
      <code className="formula">{result.formula}</code>
      <p>{result.description}</p>
      <a
        href={`${GITHUB_URL}/blob/main/${result.leanFile}`}
        className="lean-link"
        target="_blank"
        rel="noopener noreferrer"
      >
        View in Lean
      </a>
    </div>
  );
}

function BiologyCard({ result }: { result: BiologyResult }) {
  return (
    <div className="biology-card">
      <h3>{result.title}</h3>
      {result.formula && <code className="formula">{result.formula}</code>}
      <p>{result.description}</p>
      <a
        href={`${GITHUB_URL}/blob/main/${result.leanFile}`}
        className="lean-link"
        target="_blank"
        rel="noopener noreferrer"
      >
        View in Lean
      </a>
    </div>
  );
}

function App() {
  return (
    <>
      <a id="skip-to-content" href="#content">
        Skip to the content.
      </a>

      <header className="page-header">
        <DarkModeToggle />
        <div className="header-content">
          <h1 className="project-name">FUST</h1>
          <h2 className="project-tagline">Frourio Universal Structure Theorem</h2>
          <p className="project-subtitle">
            Solving the mysteries of the universe with Lean4 formal proofs
          </p>
          <div className="header-buttons">
            <a href="blueprint" className="btn btn-primary" target='_brank'>
              Blueprint (Web)
            </a>
            <a href="blueprint.pdf" className="btn" target='_brank'>
              Blueprint (PDF)
            </a>
            <a href="docs" className="btn" target='_brank'>
              Documentation
            </a>
            <a href={GITHUB_URL} className="btn" target='_brank'>
              GitHub
            </a>
          </div>
        </div>
        <GoldenSpiral width={500} height={500} className="golden-spiral" />
      </header>

      <main id="content" className="main-content">
        <section className="section millennium-section">
          <h2 className="section-title">
            <span className="section-icon">🏆</span>
            Millennium Prize Problems
          </h2>
          <p className="section-intro">
            Of the 7 Clay Mathematics Institute Millennium Problems, FUST has formally proven 2
            using Lean4's type-theoretic foundation.
          </p>
          <div className="millennium-grid">
            {millenniumProblems.map((problem) => (
              <MillenniumCard key={problem.name} problem={problem} />
            ))}
          </div>
          <div className="score-display">
            <div className="score-item solved">
              <span className="score-number">2</span>
              <span className="score-label">Solved</span>
            </div>
            <div className="score-item unsolved">
              <span className="score-number">4</span>
              <span className="score-label">Open</span>
            </div>
          </div>
        </section>

        <section className="section physics-section">
          <h2 className="section-title">
            <span className="section-icon">⚛️</span>
            Physics from First Principles
          </h2>
          <p className="section-intro">
            FUST derives fundamental physics from the golden ratio and difference operators,
            without physical postulates.
          </p>
          <div className="physics-grid">
            {physicsResults.map((result) => (
              <PhysicsCard key={result.title} result={result} />
            ))}
          </div>
        </section>

        <section className="section biology-section">
          <h2 className="section-title">
            <span className="section-icon">🧬</span>
            Biology from D-Structure
          </h2>
          <p className="section-intro">
            FUST derives biological phenomena algebraically from D-operator structure,
            including the definition of life and the necessity of sleep.
          </p>
          <div className="biology-grid">
            {biologyResults.map((result) => (
              <BiologyCard key={result.title} result={result} />
            ))}
          </div>
        </section>

        <section className="section key-results-section">
          <h2 className="section-title">
            <span className="section-icon">📐</span>
            Key Mathematical Results
          </h2>
          <div className="key-results">
            <div className="result-item">
              <h3>6-Element Completeness</h3>
              <p>
                For n ≥ 7, every difference operator Dₙ reduces to D₆ via Fibonacci closure.
                This bounds the algebraically independent operators to exactly 6.
              </p>
            </div>
            <div className="result-item">
              <h3>Gauge Parameter Space</h3>
              <p>
                FUST defines a 12-point parameter space G = G₆ × G₅ × G₁. Observer existence
                conditions select the Standard Model point SU(3) × SU(2) × U(1).
              </p>
            </div>
            <div className="result-item">
              <h3>No Selection Principles</h3>
              <p>
                Unlike anthropic reasoning, FUST derives physics from pure mathematics.
                The Standard Model is not "chosen" but emerges as the unique describable point.
              </p>
            </div>
          </div>
        </section>

        <section className="section visual-explainer-section">
          <h2 className="section-title">
            <span className="section-icon">🌌</span>
            How FUST Explains the Universe
          </h2>
          <p className="section-intro">
            Just as string theory uses "vibrating strings" to explain particles,
            FUST uses "difference operators on the golden ratio" to derive all physics.
          </p>

          <div className="visual-story">
            <div className="story-step">
              <div className="step-number">1</div>
              <div className="step-visual">
                <div className="phi-icon">φ</div>
              </div>
              <div className="step-content">
                <h3>The Golden Ratio: Nature's Most Irrational Number</h3>
                <p>
                  φ = 1.618... is not just aesthetically pleasing—it's the <strong>hardest number to approximate</strong> with fractions.
                  This mathematical property makes it the foundation of stable structures in nature.
                </p>
              </div>
            </div>

            <div className="story-step">
              <div className="step-number">2</div>
              <div className="step-visual">
                <div className="d-operator-diagram">
                  <div className="d-level">D₂</div>
                  <div className="d-arrow">↓</div>
                  <div className="d-level">D₅</div>
                  <div className="d-arrow">↓</div>
                  <div className="d-level">D₆</div>
                </div>
              </div>
              <div className="step-content">
                <h3>Difference Operators: The Universe's Building Blocks</h3>
                <p>
                  FUST defines "D operators" that measure how functions change at φ-scaled points.
                  <strong>Only D₂, D₅, and D₆ matter</strong>—higher operators reduce to D₆. This is proven, not assumed.
                </p>
              </div>
            </div>

            <div className="story-step">
              <div className="step-number">3</div>
              <div className="step-visual">
                <div className="kernel-hierarchy">
                  <div className="kernel-box ker1">dim 1</div>
                  <div className="kernel-box ker2">dim 2</div>
                  <div className="kernel-box ker3">dim 3</div>
                </div>
              </div>
              <div className="step-content">
                <h3>Kernel Dimensions: Why 3D Space?</h3>
                <p>
                  Each D operator has a "kernel"—functions it ignores. The kernel dimensions are 1, 2, 3.
                  <strong>This is why space is 3-dimensional</strong>: it's the maximum kernel dimension.
                </p>
              </div>
            </div>

            <div className="story-step">
              <div className="step-number">4</div>
              <div className="step-visual">
                <div className="gauge-groups">
                  <span className="gauge su3">SU(3)</span>
                  <span className="gauge-times">×</span>
                  <span className="gauge su2">SU(2)</span>
                  <span className="gauge-times">×</span>
                  <span className="gauge u1">U(1)</span>
                </div>
              </div>
              <div className="step-content">
                <h3>The Standard Model: Derived, Not Postulated</h3>
                <p>
                  The forces of nature (strong, weak, electromagnetic) are described by gauge groups.
                  FUST proves <strong>only SU(3)×SU(2)×U(1) can emerge</strong> from the kernel structure.
                  Grand Unified Theories (SU(5), SO(10), E₈) are mathematically excluded.
                </p>
              </div>
            </div>

            <div className="story-step">
              <div className="step-number">5</div>
              <div className="step-visual">
                <div className="mass-gap-visual">
                  <div className="energy-level vacuum">E = 0</div>
                  <div className="energy-gap">
                    <span className="gap-label">Mass Gap</span>
                  </div>
                  <div className="energy-level excited">E ≥ 36</div>
                </div>
              </div>
              <div className="step-content">
                <h3>Yang-Mills Mass Gap: Why Particles Have Mass</h3>
                <p>
                  The millennium problem asks: why is there a gap between vacuum and particles?
                  FUST answers: <strong>Δ = 2 × 3 = 6</strong> (from kernel dimensions).
                  Energy must be 0 or ≥ 36—nothing in between.
                </p>
              </div>
            </div>

            <div className="story-step">
              <div className="step-number">6</div>
              <div className="step-visual">
                <div className="time-emergence">
                  <div className="time-formula">f ∉ ker(D₆)</div>
                  <div className="time-arrow">⟹</div>
                  <div className="time-result">Time Exists</div>
                </div>
              </div>
              <div className="step-content">
                <h3>Time: An Emergent Property</h3>
                <p>
                  Photons (massless) experience no time. Why? They're in ker(D₆).
                  <strong>Time emerges only for massive particles</strong>—those outside the kernel.
                  This explains special relativity from pure algebra.
                </p>
              </div>
            </div>
          </div>

          <div className="visual-summary">
            <h3>The FUST Promise</h3>
            <p>
              String theory requires 10+ dimensions and remains unverified. FUST uses <strong>only mathematics</strong>:
              one number (φ), one family of operators (Dₙ), and rigorous proofs in Lean4.
              Every theorem is machine-verified. No hidden assumptions. No free parameters.
            </p>
          </div>
        </section>

        <section className="section cta-section">
          <h2>Explore the Proofs</h2>
          <p>
            All theorems are formally verified in Lean4. Browse the source code, run the proofs
            yourself, or contribute to extending FUST.
          </p>
          <div className="cta-buttons">
            <a href={GITHUB_URL} className="btn btn-large btn-primary" target='_brank'>
              View on GitHub
            </a>
            <a href="docs" className="btn btn-large" target='_brank'>
              Read Documentation
            </a>
          </div>
        </section>

        <footer className="site-footer">
          <div className="footer-content">
            <p className="footer-main">
              <strong>FUST</strong> is developed by{' '}
              <a href="https://frourio.com" target='_brank'>Frourio, Inc.</a>
            </p>
            <p className="footer-license">
              Released under CC0-1.0. Free for research, verification, and AI training.
            </p>
            <div className="footer-links">
              <a href={GITHUB_URL} target='_brank'>GitHub</a>
              <a href="docs" target='_brank'>Docs</a>
              <a href="blueprint" target='_brank'>Blueprint</a>
            </div>
          </div>
        </footer>
      </main>
    </>
  );
}

export default App;
