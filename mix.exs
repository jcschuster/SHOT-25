defmodule THOU.MixProject do
  use Mix.Project

  def project do
    [
      app: :thou,
      version: "0.1.0",
      elixir: "~> 1.19",
      start_permanent: Mix.env() == :prod,
      deps: deps()
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
      {:hol, "1.0.2"},
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
end
