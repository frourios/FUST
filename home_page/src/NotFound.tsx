function NotFound() {
  return (
    <>
      <a id="skip-to-content" href="#content">
        Skip to the content.
      </a>

      <header className="page-header">
        <h1 className="project-name">FUST - Frourio Universe Structure Theory</h1>
        <h2 className="project-tagline">Solving the mysteries of the universe with Lean4 formal proofs</h2>
      </header>

      <main id="content" className="main-content">
        <div className="container-404">
          <h1>404</h1>
          <p>
            <strong>Page not found :(</strong>
          </p>
          <p>The requested page could not be found.</p>
        </div>
      </main>
    </>
  );
}

export default NotFound;
