defmodule Plymio.Option.Mixfile do
  use Mix.Project

  @version "0.1.0"

  def project do
    [app: :plymio_option,
     version: @version,
     description: description(),
     package: package(),
     source_url: "https://github.com/ianrumford/plymio_option",
     homepage_url: "https://github.com/ianrumford/plymio_option",
     docs: [extras: ["./README.md", "./CHANGELOG.md"]],
     elixir: "~> 1.5",
     build_embedded: Mix.env == :prod,
     start_permanent: Mix.env == :prod,
     deps: deps()]
  end

  def application do
    [extra_applications: [:logger]]
  end

  defp deps do
    [
      {:ex_doc, "~> 0.16.4", only: :dev}
    ]
  end

  defp package do
    [maintainers: ["Ian Rumford"],
     files: ["lib", "mix.exs", "README*", "LICENSE*", "CHANGELOG*"],
     licenses: ["MIT"],
     links: %{github: "https://github.com/ianrumford/plymio_option"}]
  end

  defp description do
    """
    plymio_option: Utility Functions for Managing (Keyword) Options
    """
  end

end
