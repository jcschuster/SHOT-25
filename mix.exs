defmodule THOU.MixProject do
  use Mix.Project

  @version "0.1.0"
  @source_url "https://github.com/jcschuster/THOU"

  def project do
    [
      app: :thou,
      version: @version,
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: deps(),
      source_url: @source_url,
      description:
        "THOU (tableaux with higher-order unification) is a tableaux prover for simply-typed higher-order logic relying on higher-order pre-unification for branch closure.",
      docs: docs(),
      package: package()
    ]
  end

  # Run "mix help compile.app" to learn about applications.
  def application do
    [
      extra_applications: [:logger]
    ]
  end

  # Run "mix help deps" to learn about dependencies.
  defp deps do
    [
      {:hol, "~> 1.0.2"},
      {:behold, "~> 1.1.0"},
      {:nimble_parsec, "~> 1.4.2"},
      {:rustler, "~> 0.37.1", runtime: false},
      # Code analyzer, code duplication checker and security analyzer
      {:credo, "~> 1.7", only: [:dev, :test], runtime: false},
      # Code analyzer and type checker
      {:dialyxir, "~> 1.4", only: [:dev, :test], runtime: false},
      # Documentation generation
      {:ex_doc, "~> 0.21", only: :dev, runtime: false}
    ]
  end

  defp docs do
    [
      main: "readme",
      extras: [
        "README.md",
        "demo.livemd"
      ],
      source_url: @source_url,
      source_ref: "v#{@version}",
      before_closing_head_tag: &before_closing_head_tag/1,
      before_closing_body_tag: &before_closing_body_tag/1
    ]
  end

  defp package do
    [
      licenses: ["Apache-2.0"],
      maintainers: ["Johannes Schuster"],
      links: %{
        "GitHub" => @source_url
      },
      files: ~w(lib LICENSE mix.exs README.md)
    ]
  end

  defp before_closing_head_tag(:html) do
    """
    <link rel="stylesheet" href="https://cdn.jsdelivr.net/npm/katex@0.16.10/dist/katex.min.css">
    """
  end

  defp before_closing_head_tag(_), do: ""

  defp before_closing_body_tag(:html) do
    """
    <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.10/dist/katex.min.js"></script>
    <script defer src="https://cdn.jsdelivr.net/npm/katex@0.16.10/dist/contrib/auto-render.min.js"></script>

    <script>
      document.addEventListener("DOMContentLoaded", function() {
        var renderMath = function() {
          if (window.renderMathInElement) {
            renderMathInElement(document.body, {
              delimiters: [
                {left: "$$", right: "$$", display: true},
                {left: "$", right: "$", display: false}
              ]
            });
          }
        };

        var attempts = 0;
        var initInterval = setInterval(function() {
          if (window.renderMathInElement) {
            renderMath();
            clearInterval(initInterval);
          } else if (attempts > 20) {
            clearInterval(initInterval);
          }
          attempts++;
        }, 100);

        var observer = new MutationObserver(function(mutations) {
          observer.disconnect();
          renderMath();
          observer.observe(document.body, { childList: true, subtree: true });
        });

        observer.observe(document.body, { childList: true, subtree: true });
      });
    </script>
    """
  end

  defp before_closing_body_tag(_), do: ""
end
