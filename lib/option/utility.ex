defmodule Plymio.Option.Utility do

  @moduledoc ~S"""
  Utility Function for Managing (Keyword) Options ("opts")

  ## Documentation Terms

  In the documentation there are terms, usually in *italics*, used to mean the same thing (e.g. *opts*).

  ### opts

  *opts* is a `Keyword`.

  ### derivable opts

  *derivable opts* is either a `Keyword` or `Map` with `Atom` keys (from which the *opts* can be *derived* simply using `Map.to_list/1`).

  ### *key*

  A *key* is an `Atom`.

  ### key list

  A *key list* is a list of *key*s.

  ### key spec

  A *key spec* is usually a *key list*.

  Alternatively a `Map` with `Atom` keys or a `Keyword` can be given and the (unique) keys will be used.

  ### key alias dict

  A *key alias dict* is usually a `Map` with `Atom` keys and values used for canonicalising keys (e.g. as the 2nd argument to `opts_canonical_keys/2`).

  Alternatively a `Keyword` with `Atom` values can be given and will be converted on the fly.

  ### key dict

  A *key alias dict* is usually a `Map` with `Atom` keys.

  Alternatively a `Keyword` with `Atom` values can be given and will be converted on the fly.

  ### tuple predicate

  A *tuple predicate* is an arity one function that when passed a `{key,value}` tuple returns `true` or `false`.

  ## Return Values

  Many functions support an API that returns either `{:ok, result}` or {`:error, error}` where `error` will be an `Exception`.

  The default action for bang function when fielding `{:error, error}` is to raise the `error`.

  In many cases the `error` will be a `KeyError` where its `key` field is set to the key, or list of keys, that is missing, unknown, etc.

  """

  @type key :: atom
  @type keys :: key | [key]

  @type alias_key :: key
  @type alias_keys :: keys
  @type alias_value :: nil | alias_keys

  @type aliases_kvs :: [{alias_key, alias_value}]

  @type aliases_tuples :: [{alias_key, alias_key}]
  @type aliases_dict :: %{optional(alias_key) => alias_key}

  @type defaults_map :: %{optional(alias_key) => any}

  @type opts :: Keyword.t

  @type dict :: %{optional(alias_key) => any}

  @type error :: struct

  defdelegate opts_take_keys(arg0,arg1), to: Keyword, as: :take
  defdelegate opts_drop_keys(arg0,arg1), to: Keyword, as: :drop

  defp normalise_key_spec(value)

  defp normalise_key_spec(value) when is_list(value) do
    cond do
      Keyword.keyword?(value) -> {:ok, value |> Keyword.keys |> Enum.uniq}
      true ->
        value
        |> Enum.reject(&is_atom/1)
        |> case do
             [] -> {:ok, value |> Enum.uniq}
             not_atom_keys -> {:error, %KeyError{key: not_atom_keys, term: value}}
           end
    end
  end

  defp normalise_key_spec(value) when is_map(value) do
    value |> Map.keys |> normalise_key_spec
  end

  defp normalise_key_spec(value) do
    new_error_result(m: "expected enum", v: value)
  end

  @spec validate_key_list(any) :: {:ok, keys} | {:error, error}

  defp validate_key_list(keys)

  defp validate_key_list(keys) when is_list(keys) do

    keys
    |> Enum.reject(&is_atom/1)
    |> case do
         [] -> {:ok, keys}
         not_atoms -> not_atoms |> new_key_error_result(keys)
       end

  end

  defp validate_key_list(keys) do
    new_error_result(m: "expected valid key list", v: keys)
  end

  defp normalise_key_list(keys) do
    keys |> validate_key_list
  end

  @spec validate_key_alias_dict(any) :: {:ok, aliases_dict} | {:error, error}

  defp validate_key_alias_dict(dict)

  defp validate_key_alias_dict(dict) when is_map(dict) do

    with true <- dict |> Map.keys |> Enum.all?(&is_atom/1),
         true <- dict |> Map.values |> Enum.all?(&is_atom/1) do
      {:ok, dict}
    else
      false -> new_error_result(m: "expected valid key alias dictionary", v: dict)
    end

  end

  @spec normalise_key_alias_dict(any) :: {:ok, aliases_dict} | {:error, error}

  defp normalise_key_alias_dict(dict)

  defp normalise_key_alias_dict(dict) when is_map(dict) do
    dict |> validate_key_alias_dict
  end

  defp normalise_key_alias_dict(dict) when is_list(dict) do
    cond do
      Keyword.keyword?(dict) -> dict |> Enum.into(%{}) |> validate_key_alias_dict
      true ->
        new_error_result(m: "expected valid alias dictionary", v: dict)
    end
  end

  defp normalise_key_alias_dict(dict) do
    new_error_result(m: "expected valid alias dictionary", v: dict)
  end

  @spec validate_key_dict(any) :: {:ok, aliases_dict} | {:error, error}

  defp validate_key_dict(dict)

  defp validate_key_dict(dict) when is_map(dict) do

    with true <- dict |> Map.keys |> Enum.all?(&is_atom/1) do
      {:ok, dict}
    else
      false -> new_error_result(m: "expected valid key dictionary", v: dict)
    end

  end

  @spec normalise_key_dict(any) :: {:ok, aliases_dict} | {:error, error}

  defp normalise_key_dict(dict)

  defp normalise_key_dict(dict) when is_map(dict) do
    dict |> validate_key_dict
  end

  defp normalise_key_dict(dict) when is_list(dict) do
    cond do
      Keyword.keyword?(dict) -> dict |> Enum.into(%{})
      true ->
        new_error_result(m: "expected valid key dictionary", v: dict)
    end
  end

  defp normalise_key_dict(dict) do
    new_error_result(m: "expected valid key dictionary", v: dict)
  end

  @doc false

  defp opts_index_normalise(opts, index)

  defp opts_index_normalise(opts, index)
  when is_list(opts) and is_integer(index) and index >= 0 do
    {:ok, index}
  end

  defp opts_index_normalise(opts, index)
  when is_list(opts) and is_integer(index) and index < 0 do
    {:ok, length(opts) + index}
  end

  defp opts_index_normalise(opts, _index) when not is_list(opts) do
    new_error_result(m: "opts invalid", v: opts)
  end

  defp opts_index_normalise(_opts, index) when not is_integer(index) do
    new_error_result(m: "index invalid", v: index)
  end

  defp opts_index_validate(opts, index)
  when is_list(opts) and is_integer(index) do

    with {:ok, index} <- opts |> opts_index_normalise(index) do

      index_max = length(opts) - 1

      case index do
        x when x >= 0 -> x
        x -> index_max + x + 1
      end
      |> fn
        ndx when ndx < 0 -> new_error_result(m: :index_too_small, v: ndx)
        ndx when ndx > index_max -> new_error_result(m: :index_too_large, v: ndx)
        ndx -> {:ok, ndx}
      end.()

    else
      {:error, _} = result -> result
    end

  end

  defp opts_index_validate(opts, _index) when not is_list(opts) do
    new_error_result(m: "opts invalid", v: opts)
  end

  defp opts_index_validate(_opts, index) when not is_integer(index) do
    new_error_result(m: "index invalid", v: index)
  end

  defp opts_indices_validate(opts, indices)

  defp opts_indices_validate(opts, nil) do
    {:ok, opts |> Enum.with_index |> Enum.map(&(elem(&1,1)))}
  end

  defp opts_indices_validate(opts, indices) when is_list(opts) do

    indices
    |> List.wrap
    |> Enum.reduce({[],[]},
    fn index, {valid_indices,invalid_indices} ->

      case opts |> opts_index_validate(index) do
        {:ok, index} -> {[index | valid_indices], invalid_indices}
        {:error, _} -> {valid_indices, [index | invalid_indices]}
      end

    end)
    |> case do
         {valid_indices, []} -> {:ok, valid_indices |> Enum.reverse}
         {_valid_indices, invalid_indices} ->

           case invalid_indices |> length do
             1 -> new_error_result(m: "index invalid", v: invalid_indices |> hd)
             _ -> new_error_result(m: "indices invalid", v: invalid_indices |> Enum.reverse)
           end

       end

  end

  @doc ~S"""
  `opts_normalise/` expects a *derivable opts* and returns `{:ok, opts}`.

  Any other argument causes `{:error, error}` to be returned.

  ## Examples

      iex> [] |> opts_normalise
      {:ok, []}

      iex> %{a: 1, b: 2, c: 3} |> opts_normalise
      {:ok, [a: 1, b: 2, c: 3]}

      iex> %{"a" => 1, :b => 2, :c => 3} |> opts_normalise
      {:error, %KeyError{key: "a", term: %{:b => 2, :c => 3, "a" => 1}}}

      iex> 42 |> opts_normalise
      {:error, %ArgumentError{message: "expected valid derivable opts; got: 42"}}

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_normalise
      {:ok, [a: nil, b: [:b1], c: [:c1, :c2, :c3]]}

  """

  @spec opts_normalise(any) :: {:ok, opts} | {:error, error}

  def opts_normalise(value) do

    cond do
      Keyword.keyword?(value) -> {:ok, value}

      is_map(value) ->

        value
        |> Map.to_list
        |> fn tuples ->
          tuples
          |> Keyword.keyword?
          |> case do
               true -> {:ok, tuples}
               _ ->

                 tuples
                 |> Keyword.keys
                 |> Enum.reject(&is_atom/1)
                 |> new_key_error_result(value)

             end
        end.()

      true -> new_error_result(m: "expected valid derivable opts", v: value)

    end

  end

  @doc ~S"""
  `opts_normalise!/1` calls `opts_normalise/1` and if the result is `{:ok, opts}` returns `opts`.

  ## Examples

      iex> [] |> opts_normalise!
      []

      iex> %{a: 1, b: 2, c: 3} |> opts_normalise!
      [a: 1, b: 2, c: 3]

      iex> %{"a" => 1, :b => 2, :c => 3} |> opts_normalise!
      ** (KeyError) key "a" not found in: %{:b => 2, :c => 3, "a" => 1}

      iex> 42 |> opts_normalise!
      ** (ArgumentError) expected valid derivable opts; got: 42

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_normalise!
      [a: nil, b: [:b1], c: [:c1, :c2, :c3]]

  """

  @spec opts_normalise!(any) :: opts | no_return

  def opts_normalise!(opts) do
    case opts |> opts_normalise do
      {:ok, opts} -> opts
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_normalise_map/` expects a *derivable opts* as argument.

  If the argument is a `Map`, with `Atom` keys, it returns `{:ok, argument}` directly.

  If the argument is a `Keyword`, with `Atom` keys, it returns `{:ok, argument |> Enum.into(%{})}`.

  Any other argument causes `{:error, error}` to be returned.

  ## Examples

      iex> [] |> opts_normalise_map
      {:ok, %{}}

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_normalise_map
      {:ok, %{a: nil, b: [:b1], c: [:c1, :c2, :c3]}}

      iex> %{a: 1, b: 2, c: 3} |> opts_normalise_map
      {:ok, %{a: 1, b: 2, c: 3}}

      iex> %{"a" => 1, :b => 2, :c => 3} |> opts_normalise_map
      {:error, %KeyError{key: ["a"], term: %{:b => 2, :c => 3, "a" => 1}}}

      iex> 42 |> opts_normalise_map
      {:error, %ArgumentError{message: "expected valid derivable opts; got: 42"}}

  """

  @spec opts_normalise_map(any) :: {:ok, opts} | {:error, error}

  def opts_normalise_map(value) do

    cond do

      Keyword.keyword?(value) -> {:ok, value |> Enum.into(%{})}

      is_map(value) ->

        with {:ok, _} <- value |> normalise_key_spec do
          {:ok, value}
        else
          {:error, %KeyError{} = error} -> {:error, struct!(error, term: value)}
          {:error, _} = result -> result
        end

      true -> new_error_result(m: "expected valid derivable opts", v: value)

    end
  end

  @doc ~S"""
  `opts_normalise_map!/1` call `opts_normalise_map/1` and if the result is `{:ok, map}` returns `map`.

  ## Examples

      iex> [] |> opts_normalise_map!
      %{}

      iex> [a: 1, b: 2, c: 3] |> opts_normalise_map!
      %{a: 1, b: 2, c: 3}

      iex> %{a: 1, b: 2, c: 3} |> opts_normalise_map!
      %{a: 1, b: 2, c: 3}

      iex> %{"a" => 1, :b => 2, :c => 3} |> opts_normalise_map!
      ** (KeyError) key ["a"] not found in: %{:b => 2, :c => 3, "a" => 1}

      iex> 42 |> opts_normalise_map!
      ** (ArgumentError) expected valid derivable opts; got: 42

  """

  @spec opts_normalise_map!(any) :: opts | no_return

  def opts_normalise_map!(opts) do
    case opts |> opts_normalise_map do
      {:ok, map} -> map
      {:error, %KeyError{} = error} -> raise struct!(error, term: opts)
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_validate/1` returns `{:ok, opts}` if the argument is an *opts*.

  Any other argument causes `{:error, error}` to be returned.

  ## Examples

      iex> [] |> opts_validate
      {:ok, []}

      iex> %{a: 1, b: 2, c: 3} |> opts_validate
      {:error, %ArgumentError{message: "validate opts failed; got: %{a: 1, b: 2, c: 3}"}}

      iex> %{"a" => 1, :b => 2, :c => 3} |> opts_validate
      {:error, %ArgumentError{message: "validate opts failed; got: %{:b => 2, :c => 3, \"a\" => 1}"}}

      iex> 42 |> opts_validate
      {:error, %ArgumentError{message: "validate opts failed; got: 42"}}

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_validate
      {:ok, [a: nil, b: [:b1], c: [:c1, :c2, :c3]]}

  """

  @spec opts_validate(any) :: {:ok, opts} | {:error, error}

  def opts_validate(value) do
    case Keyword.keyword?(value) do
      true -> {:ok, value}
      _  -> new_error_result(m: "validate opts failed", v: value)
    end
  end

  @doc ~S"""
  `opts_validate!/1` calls `opts_validate/1` and, if the result is `{:ok, opts}`, returns `opts`.

  ## Examples

      iex> [] |> opts_validate!
      []

      iex> %{a: 1, b: 2, c: 3} |> opts_validate!
      ** (ArgumentError) validate opts failed; got: %{a: 1, b: 2, c: 3}

      iex> %{"a" => 1, :b => 2, :c => 3} |> opts_validate!
      ** (ArgumentError) validate opts failed; got: %{:b => 2, :c => 3, "a" => 1}

      iex> 42 |> opts_validate!
      ** (ArgumentError) validate opts failed; got: 42

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_validate!
      [a: nil, b: [:b1], c: [:c1, :c2, :c3]]

  """

  @spec opts_validate!(opts) :: opts | no_return

  def opts_validate!(opts) do
    case opts |> opts_validate do
      {:ok, opts} -> opts
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_create_aliases_tuples/1` takes an *opts* where the keys are the canonical key names, and their values are zero (nil), one or more aliases for the canonical key.

  A `Keyword` is returned where each key is an alias and its value the canonical key.

  The canonical key also has an entry for itself with the same value.

  ## Examples

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_create_aliases_tuples
      [a: :a, b: :b, b1: :b, c: :c, c1: :c, c2: :c, c3: :c]

  """

  @spec opts_create_aliases_tuples(aliases_kvs) :: aliases_tuples

  def opts_create_aliases_tuples(aliases) do

    aliases
    |> Enum.map(fn

      {k,nil} -> {k,k}

      {k,a} ->

        [k | a |> List.wrap]
        |> Enum.uniq
        |> Enum.map(fn a -> {a,k} end)

    end)
    |> List.flatten

  end

  @doc ~S"""
  `opts_create_aliases_dict/1` does the same job as `opts_create_aliases_tuples/1` but returns a *key alias dict*.

  ## Examples

      iex> [a: nil, b: [:b1], c: [:c1, :c2, :c3]] |> opts_create_aliases_dict
      %{a: :a, b: :b, b1: :b, c: :c, c1: :c, c2: :c, c3: :c}

  """

  @spec opts_create_aliases_dict(aliases_kvs) :: aliases_dict

  def opts_create_aliases_dict(aliases) do

    aliases
    |> opts_create_aliases_tuples
    |> Enum.into(%{})

  end

  @doc ~S"""
  `opts_create_defstruct/2` takes an *opts*, together with a defaults map, and returns an *opts*  where each value if the value of the key in the defaults map (with default `nil`).

  `opts_create_defstruct/2` creates an argument suitable for use with `Kernel.defstruct/1`

  The defaults map must contain *only*  keys that are also in the opts list; any unknown keys will raise a `KeyError.`

  ## Examples

      iex> [a: 1, b: :two, c: "tre", d: nil] |> opts_create_defstruct(%{a: 42, b: "two"})
      [a: 42, b: "two", c: nil, d: nil]

      iex> [a: 1, b: :two, c: "tre", d: nil] |> opts_create_defstruct(%{a: 42, b: "two", x: 1})
      ** (KeyError) key [:x] not found in: [a: 1, b: :two, c: "tre", d: nil]

  """

  @spec opts_create_defstruct(opts, defaults_map) :: opts

  def opts_create_defstruct(struct_kvs, defaults_map \\ %{})

  def opts_create_defstruct(struct_kvs, defaults_map)
  when is_map(defaults_map) and (map_size(defaults_map) == 0) do
    struct_kvs |> Enum.map(fn {k,_v} -> {k,nil} end)
  end

  def opts_create_defstruct(struct_kvs, defaults_map)
  when is_map(defaults_map) do

    # do not allow keys in the default that aren't in the struct_kvs
    # too dangerous as hard to spot e.g default with wrong name

    struct_map = struct_kvs |> Map.new(fn {k,_v} -> {k, nil} end)

    defaults_map
    # get rid of known keys
    |> Enum.reject(fn {k,_v} -> struct_map |> Map.has_key?(k) end)
    |> Keyword.keys
    |> case do

         # no unknown keys
         [] -> nil

         unknown_keys ->

           raise KeyError, key: unknown_keys, term: struct_kvs

       end

    struct_kvs
    |> Enum.map(fn {k,_v} -> {k, defaults_map |> Map.get(k)} end)

  end

  @doc ~S"""
  `opts_crue_defstruct/2` takes a *derivable opts*, together with a defaults map, and returns `{:ok, opts}` where each value is the value of the key in the defaults map (with default `nil`).

  `opts_crue_defstruct/2` creates an argument suitable for use with `Kernel.defstruct/1`

  The defaults map must contain *only*  keys that are also in the opts list; any unknown keys will cause `{:error, error}`, where `error` is a `KeyError`, to be returned.

  ## Examples

      iex> [a: 1, b: :two, c: "tre", d: nil] |> opts_crue_defstruct(%{a: 42, b: "two"})
      {:ok, [a: 42, b: "two", c: nil, d: nil]}

      iex> [a: 1, b: :two, c: "tre", d: nil] |> opts_crue_defstruct(%{a: 42, b: "two", x: 1})
      {:error, %KeyError{key: :x, term: [a: 1, b: :two, c: "tre", d: nil]}}

  """

  @spec opts_crue_defstruct(opts, defaults_map) :: {:ok, opts} | {:error, error}

  def opts_crue_defstruct(struct_kvs, defaults_map \\ %{})

  def opts_crue_defstruct(struct_kvs, defaults_map)
  when is_map(defaults_map) and (map_size(defaults_map) == 0) do
    {:ok, struct_kvs |> Enum.map(fn {k,_v} -> {k,nil} end)}
  end

  def opts_crue_defstruct(struct_kvs, defaults_map)
  when is_map(defaults_map) do

    with {:ok, struct_kvs} <- struct_kvs |> opts_normalise do

      # do not allow keys in the default that aren't in the struct_kvs
      # too dangerous as hard to spot e.g default with wrong name

      struct_map = struct_kvs |> Map.new(fn {k,_v} -> {k, nil} end)

      defaults_map
      # get rid of known keys
      |> Enum.reject(fn {k,_v} -> struct_map |> Map.has_key?(k) end)
      |> Keyword.keys
      |> case do

           # no unknown keys
           [] -> {:ok, struct_kvs |> Enum.map(fn {k,_v} -> {k, defaults_map |> Map.get(k)} end)}

           unknown_keys -> unknown_keys |> new_key_error_result(struct_kvs)

         end
    else
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `opts_crue_defstruct!/2` calls `opts_crue_defstruct/2` and if the result is `{:ok, opts}` returns `opts`.

  ## Examples

      iex> [a: 1, b: :two, c: "tre", d: nil] |> opts_crue_defstruct!(%{a: 42, b: "two"})
      [a: 42, b: "two", c: nil, d: nil]

      iex> [a: 1, b: :two, c: "tre", d: nil] |> opts_crue_defstruct!(%{a: 42, b: "two", x: 1})
      ** (KeyError) key :x not found in: [a: 1, b: :two, c: "tre", d: nil]

  """

  @spec opts_crue_defstruct!(opts, defaults_map) :: opts | no_return

  def opts_crue_defstruct!(struct_kvs, defaults_map \\ %{})

  def opts_crue_defstruct!(opts, defaults_map) do
    case opts_crue_defstruct(opts, defaults_map) do
      {:ok, opts} -> opts
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_avoir_keys/2` takes an *opts* and a *key spec*.

  If all of the keys are present in the `opts`, its returns `{:ok, opts}`.

  If there are any missing keys, `{:error, error}`, where `error` is a `KeyError`, will be returned.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys([:a, :b, :c])
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys(%{a: 1, b: 2, c: 3})
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys([:a, :b, :d, :a])
      {:error, %KeyError{key: :d, term: [a: 1, b: 2, c: 3]}}

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys(%{x: nil, y: nil, z: nil})
      {:error, %KeyError{key: [:x, :y, :z], term: [a: 1, b: 2, c: 3]}}

  """

  @spec opts_avoir_keys(any, any) :: {:ok, opts} | {:error, error}

  def opts_avoir_keys(opts, keys)

  def opts_avoir_keys(opts, keys) do

    with {:ok, opts_keys} <- opts |> normalise_key_spec,
         {:ok, wanted_keys} <- keys |> normalise_key_spec do

      wanted_keys -- opts_keys
      |> case do

           # none missing
           [] -> {:ok, opts}

           missing_keys -> missing_keys |> new_key_error_result(opts)

         end
    else
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `opts_avoir_keys?/2` calls `opts_avoir_keys/2` and if the result is `{:ok, _}`, returns `true`, else `false`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys?([:a, :b, :c])
      true

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys?(%{a: 1, b: 2, c: 3})
      true

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys?([:a, :b, :d, :a])
      false

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys?(%{x: nil, y: nil, z: nil})
      false

  """

  @spec opts_avoir_keys?(any, any) :: true | false

  def opts_avoir_keys?(opts, keys) do
    case opts_avoir_keys(opts, keys) do
      {:ok, _} -> true
      _ -> false
    end
  end

  @doc ~S"""
  `opts_avoir_keys!/2` calls `opts_avoir_keys/2` and if the result is `{:ok, opts}`, returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys!([:a, :b, :c])
      [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys!(%{a: 1, b: 2, c: 3})
      [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys!([:a, :b, :d, :a])
      ** (KeyError) key :d not found in: [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_avoir_keys!(%{x: nil, y: nil, z: nil})
      ** (KeyError) key [:x, :y, :z] not found in: [a: 1, b: 2, c: 3]

  """

  @spec opts_avoir_keys!(any, any) :: opts | no_return

  def opts_avoir_keys!(opts, keys) do
    case opts_avoir_keys(opts, keys) do
      {:ok, opts} -> opts
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_has_keys/2` takes an *opts*, together with a list or dictionary (map) of wanted `keys`.

  If all of the `keys` are present in the `opts`, its returns `{:ok, opts}`.

  If there are any missing keys, `{:error, {present_opts, missing_keys}}` is returned, where the
  `present_opts` include *only* the tuples for the wanted keys (i.e. result of `Keyword.take/2` for the wanted keys).

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys([:a, :b, :c])
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys(%{a: 1, b: 2, c: 3})
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys([:a, :b, :d, :a])
      {:error, {[a: 1, b: 2], [:d]}}

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys(%{x: nil, y: nil, z: nil})
      {:error, {[], [:x, :y, :z]}}

  """

  @spec opts_has_keys(opts, keys) :: {:ok, opts} | {:error, {opts,opts}}
  @spec opts_has_keys(opts, dict) :: {:ok, opts} | {:error, {opts,opts}}

  def opts_has_keys(opts, keys_or_dict)

  def opts_has_keys(opts, dict) when is_map(dict) do

    opts
    |> opts_has_keys(dict |> Map.keys)

  end

  def opts_has_keys(opts, keys) when is_list(keys) do

    opts_keys = opts |> Keyword.keys |> Enum.uniq

    wanted_keys = keys |> Enum.uniq

    wanted_keys -- opts_keys
    |> case do

         # none missing
         [] -> {:ok, opts}

         missing_keys ->

           wanted_tuples = opts |> opts_take_keys(wanted_keys)

           {:error, {wanted_tuples, missing_keys}}

       end

  end

  @doc ~S"""
  `opts_has_keys?/2` calls `opts_has_keys/2` and if the result is `{:ok, _}`, returns `true`, else `false`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys?([:a, :b, :c])
      true

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys?(%{a: 1, b: 2, c: 3})
      true

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys?([:a, :b, :d, :a])
      false

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys?(%{x: nil, y: nil, z: nil})
      false

  """

  @spec opts_has_keys?(opts, keys) :: true | false
  @spec opts_has_keys?(opts, dict) :: true | false

  def opts_has_keys?(opts, keys) do
    case opts_has_keys(opts, keys) do
      {:ok, _} -> true
      _ -> false
    end
  end

  @doc ~S"""
  `opts_has_keys!/2` calls `opts_has_keys/2` and if the result is `{:ok, opts}`, returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys!([:a, :b, :c])
      [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys!(%{a: 1, b: 2, c: 3})
      [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys!([:a, :b, :d, :a])
      ** (KeyError) key [:d] not found in: [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_has_keys!(%{x: nil, y: nil, z: nil})
      ** (KeyError) key [:x, :y, :z] not found in: [a: 1, b: 2, c: 3]

  """

  @spec opts_has_keys!(opts, keys) :: opts | no_return
  @spec opts_has_keys!(opts, dict) :: opts | no_return

  def opts_has_keys!(opts, keys) do
    case opts_has_keys(opts, keys) do
      {:ok, x} -> x
      {:error, {_present_tuples, missing_keys}} ->

        raise KeyError, key: missing_keys, term: opts

    end

  end

  @doc ~S"""
  `opts_canon_keys!/2` takes an *opts*, together with a lookup dictionary and replaces each key with its canonical value from the dictionary. Unknown keys raise a `KeyError`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_canon_keys!(%{a: :x, b: :y, c: :z})
      [x: 1, y: 2, z: 3]

      iex> [x: 1, y: 3, z: 3] |> opts_canon_keys!(%{a: 1, b: 2, c: 3})
      ** (KeyError) key :x not found in: %{a: 1, b: 2, c: 3}

  """

  @spec opts_canon_keys!(opts, dict) :: opts | no_return

  def opts_canon_keys!(opts, dict) when is_map(dict) do
    opts |> Enum.map(fn {k,v} -> {dict |> Map.fetch!(k), v} end)
  end

  @doc ~S"""
  `opts_canon_keys/2` takes an *opts*, together with either a dictionary (map) or (keyword) list of aliases.

  If a dictionary is provided, each key in the `opts` is replaced with its (canonical) value from the dictionary, returning `{:ok, transformed_opts}`.

  If a (keyword) list of aliases is provided, the aliases are first converted into a dictionary by `opts_create_aliases_dict/1` and the dictionary used as described above.

  If there are any unknown keys, `{:error, {known_opts, unknown_opts}}` is returned.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_canon_keys(%{a: :x, b: :y, c: :z})
      {:ok, [x: 1, y: 2, z: 3]}

      iex> [a: 11, p: 1, b: 22, q: 2, c: 33, r: 3] |> opts_canon_keys(%{a: :x, b: :y, c: :z})
      {:error, {[x: 11, y: 22, z: 33], [p: 1, q: 2, r: 3]}}

      iex> [a: 1, b: 2, c: 3] |> opts_canon_keys([a_canon: :a, b_canon: [:b], c_canon: [:c, :cc]])
      {:ok, [a_canon: 1, b_canon: 2, c_canon: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_canon_keys([a_canon: :a, b_canon: nil, c_canon: [:c, :cc]])
      {:error, {[a_canon: 1, c_canon: 3], [b: 2]}}

  """

  @spec opts_canon_keys(opts, dict) :: {:ok, opts} | {:error, {opts, opts}}
  @spec opts_canon_keys(opts, opts) :: {:ok, opts} | {:error, {opts, opts}}

  def opts_canon_keys(opts, dict) when is_map(dict) do

    opts
    # split into known and unknown keys
    |> Enum.split_with(fn {k,_v} -> Map.has_key?(dict, k) end)
    |> case do

         # no unknown keys
         {known_tuples, []} ->
           {:ok, opts_canon_keys!(known_tuples, dict)}

         {known_tuples, unknown_tuples} ->
           {:error, {opts_canon_keys!(known_tuples, dict), unknown_tuples}}

       end

  end

  def opts_canon_keys(opts, aliases) when is_list(aliases) do

    opts
    |> opts_canon_keys(aliases |> opts_create_aliases_dict)

  end

  @doc ~S"""
  `opts_canonical_keys/2` takes a *derivable opts*, together with a *key alias dict*.

  Each key in the `opts` is replaced with its (canonical) value from the dictionary, returning `{:ok, canon_opts}`.

  If there are any unknown keys, `{:error, error}`, where `error` is a `KeyError`, will be returned.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_canonical_keys(%{a: :x, b: :y, c: :z})
      {:ok, [x: 1, y: 2, z: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_canonical_keys([a: :x, b: :y, c: :z])
      {:ok, [x: 1, y: 2, z: 3]}

      iex> [a: 11, p: 1, b: 22, q: 2, c: 33, r: 3] |> opts_canonical_keys(%{a: :x, b: :y, c: :z})
      {:error, %KeyError{key: [:p, :q, :r], term: %{a: :x, b: :y, c: :z}}}

      iex> [a: 1, b: 2, c: 3] |> opts_canonical_keys([a_canon: :a, b_canon: [:b], c_canon: [:c, :cc]])
      {:error, %ArgumentError{message: "expected valid key alias dictionary; got: %{a_canon: :a, b_canon: [:b], c_canon: [:c, :cc]}"}}

  """

  @spec opts_canonical_keys(any, any) :: {:ok, opts} | {:error, error}

  def opts_canonical_keys(opts, dict) do

    with {:ok, opts} <- opts |> opts_normalise,
         {:ok, dict} <- dict |> normalise_key_alias_dict do

      opts
      # reject known_keys
      |> Enum.reject(fn {k,_v} -> Map.has_key?(dict, k) end)
      |> case do

           # no unknown keys
           [] ->

           canon_tuples = opts
           |> Enum.map(fn{k,v} -> {Map.get(dict,k), v} end)

           {:ok, canon_tuples}

         unknown_tuples -> unknown_tuples |> new_key_error_result(dict)

       end
    else
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `opts_canonical_keys!/2` calls `opts_canonical_keys/2` and if the result is `{:ok, opts}` returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_canonical_keys!(%{a: :x, b: :y, c: :z})
      [x: 1, y: 2, z: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_canonical_keys!([a: :x, b: :y, c: :z])
      [x: 1, y: 2, z: 3]

      iex> [x: 1, y: 3, z: 3] |> opts_canonical_keys!(%{a: 1, b: 2, c: 3})
      ** (ArgumentError) expected valid key alias dictionary; got: %{a: 1, b: 2, c: 3}

  """

  @spec opts_canonical_keys!(any, any) :: opts | no_return

  def opts_canonical_keys!(opts, dict) do
    with {:ok, opts} <- opts |> opts_canonical_keys(dict) do
      opts
    else
      {:error, error} -> raise error
    end
  end

  @doc ~S"""

  `opts_sort_keys/` takes a *derivable opts*, together with a list of sort keys, and returns the opts sorted in the sort keys order. Duplicate keys follow one after another.

  Any keys found but not given in the sort keys follow the sorted keys in the returned opts.

  Any key in the sort list not found in the opts is ignored.

  ## Examples

      iex> [a: 1, b: 2, c: 3, d: 4] |> opts_sort_keys
      [a: 1, b: 2, c: 3, d: 4]

      iex> [a: 1, b: 2, c: 3, d: 4] |> opts_sort_keys([:c, :a])
      [c: 3, a: 1,  b: 2, d: 4]

      iex> [] |> opts_sort_keys([:c, :a])
      []

      iex> [a: 11, b: 2, c: 3, a: 12, d: 4] |> opts_sort_keys([:c, :a])
      [c: 3, a: 11, a: 12, b: 2, d: 4]

      iex> [a: 11, b: 21, c: 3, a: 12, d: 4, b: 22] |> opts_sort_keys([:d, :x, :b, :z])
      [d: 4, b: 21, b: 22, a: 11, c: 3, a: 12]

  """

  @spec opts_sort_keys(any, any) :: {:ok, opts} | {:error, error}

  def opts_sort_keys(opts, keys \\ [])

  def opts_sort_keys([], _keys) do
    []
  end

  def opts_sort_keys(opts, keys) do

    sort_keys = keys |> Enum.uniq

    sort_dict = sort_keys |> Map.new(fn k -> {k,nil} end)

    # partition the opts into sort and other keys
    {sorted_tuples, remain_tuples} = opts
    |> Enum.split_with(fn {k,_v} -> Map.has_key?(sort_dict, k) end)

    # collect the sorted_tuples for same key
    sort_keys
    |> Enum.flat_map(fn k ->
      sorted_tuples
      |> Keyword.get_values(k)
      |> Enum.map(fn v -> {k,v} end)
    end)
    |> Kernel.++(remain_tuples)

  end

  @doc ~S"""
  `opts_take_keys!/1` takes an *opts*, together with a *key list* and returns the *opts* with just the supplied keys.

  It any of the keys are not found, raises a `KeyError` citing the missing keys.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_take_keys!([:c, :a])
      [a: 1, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_take_keys!([:d, :a])
      ** (KeyError) key [:d] not found in: [a: 1, b: 2, c: 3]

  """

  @spec opts_take_keys!(opts, keys) :: opts

  def opts_take_keys!(opts, keys \\ [])

  def opts_take_keys!([], _keys) do
    []
  end

  def opts_take_keys!(opts, []) when is_list(opts) do
    []
  end

  def opts_take_keys!(opts, keys) when is_list(keys) do

    opts
    |> opts_take_keys(keys)
    # check all keys present
    |> opts_has_keys(keys)
    |> case do

      {:ok, new_opts} -> new_opts

      {:error, {_present_opts, missing_keys}} ->

        raise KeyError, key: missing_keys, term: opts

    end

  end

  @doc ~S"""
  `opts_drop_keys!/1` takes an *opts*, together with a *key list* and returns the *opts* without the supplied keys.

  It any of the keys are not found, raises a `KeyError` citing the missing keys.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_drop_keys!([:b])
      [a: 1, c: 3]

      iex> [a: 11, b: 21, c: 3, b: 22, a: 12] |> opts_drop_keys!([:b])
      [a: 11, c: 3, a: 12]

      iex> [a: 1, b: 2, c: 3] |> opts_drop_keys!([:d, :a])
      ** (KeyError) key [:d] not found in: [a: 1, b: 2, c: 3]

  """

  @spec opts_drop_keys!(opts, keys) :: opts

  def opts_drop_keys!(opts, keys \\ [])

  def opts_drop_keys!([], _keys) do
    []
  end

  def opts_drop_keys!(opts, []) when is_list(opts) do
    []
  end

  def opts_drop_keys!(opts, keys) when is_list(keys) do

    opts
    |> opts_has_keys(keys)
    |> case do

         {:ok, _} -> opts |> opts_drop_keys(keys)

         {:error, {_present_opts, missing_keys}} ->

        raise KeyError, key: missing_keys, term: opts

    end

  end

  @doc ~S"""
  `opts_filter/2` takes a *derivable opts*, together with a *tuple predicate* and returns `{:ok, opts}` where `opts` has all the 2tuples the *tuple predicate* return `true` for.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_filter(&(&1))
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_filter(
      ...>   fn
      ...>   {:a,_} -> true
      ...>   _ -> false
      ...>   end)
      {:ok, [a: 1]}

      iex> %{a: 1, b: 2, c: 3} |> opts_filter(
      ...>   fn
      ...>   {:a,_} -> false
      ...>   _ -> true
      ...>   end)
      {:ok, [b: 2, c: 3]}

      iex> {:error, error} = [a: 1, b: 2, c: 3] |> opts_filter(:not_a_function)
      ...> match?(%ArgumentError{message: "expected valid tuple predicate; got: :not_a_function"}, error)
      true

      iex> {:error, error} = :not_opts |> opts_filter(&(&1))
      ...> match?(%ArgumentError{message: "expected valid derivable opts; got: :not_opts"}, error)
      true

  """

  @spec opts_filter(any, any) :: {:ok, opts} | {:error, error}

  def opts_filter(opts, fun_pred)  when is_function(fun_pred,1) do

    with {:ok, opts} <- opts |> opts_normalise do

      opts = opts
      |> Enum.filter(fun_pred)

      {:ok, opts}

    else
      {:error, _} = result -> result
    end

  end

  def opts_filter(_opts, fun_pred)  do
    new_error_result(m: "expected valid tuple predicate", v: fun_pred)
  end

  @doc ~S"""
  `opts_filter!/2` calls `opts_filter/2` and if the result is `{:ok, opts}` returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_filter!(&(&1))
      [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_filter!(
      ...>   fn
      ...>   {:a,_} -> true
      ...>   _ -> false
      ...>   end)
      [a: 1]

      iex> %{a: 1, b: 2, c: 3} |> opts_filter!(
      ...>   fn
      ...>   {:a,_} -> false
      ...>   _ -> true
      ...>   end)
      [b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_filter!(:not_a_function)
      ** (ArgumentError) expected valid tuple predicate; got: :not_a_function

      iex> :not_opts |> opts_filter!(&(&1))
      ** (ArgumentError) expected valid derivable opts; got: :not_opts

  """

  @spec opts_filter!(any, any) :: opts | no_return

  def opts_filter!(opts, dict) do
    with {:ok, opts} <- opts |> opts_filter(dict) do
      opts
    else
      {:error, error} -> raise error
    end
  end

  @doc ~S"""
  `opts_reject/2` takes a *derivable opts*, together with a *tuple predicate* and returns `{:ok, opts}` where `opts` has all the 2tuples the *tuple predicate* returns `false` for.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_reject(&(&1))
      {:ok, []}

      iex> [a: 1, b: 2, c: 3] |> opts_reject(
      ...>   fn
      ...>   {:a,_} -> true
      ...>   _ -> false
      ...>   end)
      {:ok, [b: 2, c: 3]}

      iex> %{a: 1, b: 2, c: 3} |> opts_reject(
      ...>   fn
      ...>   {:a,_} -> false
      ...>   _ -> true
      ...>   end)
      {:ok, [a: 1]}

      iex> {:error, error} = [a: 1, b: 2, c: 3] |> opts_reject(:not_a_function)
      ...> match?(%ArgumentError{message: "expected valid tuple predicate; got: :not_a_function"}, error)
      true

      iex> {:error, error} = :not_opts |> opts_reject(&(&1))
      ...> match?(%ArgumentError{message: "expected valid derivable opts; got: :not_opts"}, error)
      true

  """

  @spec opts_reject(any, any) :: {:ok, opts} | {:error, error}

  def opts_reject(opts, fun_pred)  when is_function(fun_pred,1) do

    with {:ok, opts} <- opts |> opts_normalise do

      opts = opts
      |> Enum.reject(fun_pred)

      {:ok, opts}

    else
      {:error, _} = result -> result
    end

  end

  def opts_reject(_opts, fun_pred)  do
    new_error_result(m: "expected valid tuple predicate", v: fun_pred)
  end

  @doc ~S"""
  `opts_reject!/2` calls `opts_reject/2` and if the result is `{:ok, opts}` returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_reject!(&(&1))
      []

      iex> [a: 1, b: 2, c: 3] |> opts_reject!(
      ...>   fn
      ...>   {:a,_} -> true
      ...>   _ -> false
      ...>   end)
      [b: 2, c: 3]

      iex> %{a: 1, b: 2, c: 3} |> opts_reject!(
      ...>   fn
      ...>   {:a,_} -> false
      ...>   _ -> true
      ...>   end)
      [a: 1]

      iex> [a: 1, b: 2, c: 3] |> opts_reject!(:not_a_function)
      ** (ArgumentError) expected valid tuple predicate; got: :not_a_function

      iex> :not_opts |> opts_reject!(&(&1))
      ** (ArgumentError) expected valid derivable opts; got: :not_opts

  """

  @spec opts_reject!(any, any) :: opts | no_return

  def opts_reject!(opts, dict) do
    with {:ok, opts} <- opts |> opts_reject(dict) do
      opts
    else
      {:error, error} -> raise error
    end
  end

  @doc ~S"""
  `opts_predicate/2` takes a *derivable opts*, together with a *tuple predicate* and returns `{:ok, opts}` if all the 2tuples pass the *tuple predicate*.

  If any of the *opts* fail the *tuple predicate*, {:error, error} is returned where `error` will be a `KeyError` whose `key` field contains all the keys that failed.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_predicate(&(&1))
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_predicate(fn {_k,v} -> v |> is_integer end)
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_predicate(
      ...>   fn
      ...>   {:a,_} -> true
      ...>   _ -> false
      ...>   end)
      {:error, %KeyError{key: [:b, :c], term: [a: 1, b: 2, c: 3]}}

      iex> {:error, error} = [a: 1, b: 2, c: 3] |> opts_predicate(:not_a_function)
      ...> match?(%ArgumentError{message: "expected valid tuple predicate; got: :not_a_function"}, error)
      true

      iex> {:error, error} = :not_opts |> opts_predicate(&(&1))
      ...> match?(%ArgumentError{message: "expected valid derivable opts; got: :not_opts"}, error)
      true

  """

  @spec opts_predicate(any, any) :: {:ok, opts} | {:error, error}

  def opts_predicate(opts, fun_pred)  when is_function(fun_pred,1) do

    with {:ok, norm_opts} <- opts |> opts_normalise do

      norm_opts
      |> Enum.split_with(fun_pred)
      |> case do

           {pass_opts, []} -> {:ok, pass_opts}

           {_pass_opts, fail_opts} ->

             # build a KeyError with failing keys
             fail_keys = fail_opts |> Keyword.keys |> Enum.uniq

             {:error, %KeyError{key: fail_keys, term: opts}}

         end

    else
      {:error, _} = result -> result
    end

  end

  def opts_predicate(_opts, fun_pred)  do
    new_error_result(m: "expected valid tuple predicate", v: fun_pred)
  end

  @doc ~S"""
  `opts_predicate!/2` calls `opts_predicate/2` and if the result is `{:ok, opts}` returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_predicate(&(&1))
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_predicate(fn {_k,v} -> v |> is_integer end)
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_predicate(
      ...>   fn
      ...>   {:a,_} -> true
      ...>   _ -> false
      ...>   end)
      {:error, %KeyError{key: [:b, :c], term: [a: 1, b: 2, c: 3]}}

      iex> [a: 1, b: 2, c: 3] |> opts_predicate!(:not_a_function)
      ** (ArgumentError) expected valid tuple predicate; got: :not_a_function

      iex> :not_opts |> opts_predicate!(&(&1))
      ** (ArgumentError) expected valid derivable opts; got: :not_opts

  """

  @spec opts_predicate!(any, any) :: opts | no_return

  def opts_predicate!(opts, dict) do
    with {:ok, opts} <- opts |> opts_predicate(dict) do
      opts
    else
      {:error, error} -> raise error
    end
  end

  @doc ~S"""
  `opts_filter_keys/2` takes a *derivable opts* and a *key spec* and returns `{:ok, opts}` where `opts` has all keys from the original *derivable opts* that appear in the *key spec*.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys([:a, :b, :c])
      {:ok, [a: 1, b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys([b: :want_b, c: :and_c])
      {:ok, [b: 2, c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys(%{a: 42, b: nil})
      {:ok, [a: 1, b: 2]}

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys(:not_a_key_spec)
      {:error, %ArgumentError{message: "expected enum; got: :not_a_key_spec"}}

      iex> :not_opts |> opts_filter_keys([:a, :b, :c])
      {:error, %ArgumentError{message: "expected valid derivable opts; got: :not_opts"}}

  """

  @spec opts_filter_keys(any, any) :: {:ok, opts} | {:error, error}

  def opts_filter_keys(opts, keys)

  def opts_filter_keys(opts, keys) do

    with {:ok, filter_keys} <- keys |> normalise_key_spec do

      filter_map = filter_keys |> Map.new(fn k -> {k, nil} end)

      filter_pred = fn {k,_v} -> filter_map |> Map.has_key?(k) end

      with {:ok, _filter_opts} = result <- opts |> opts_filter(filter_pred) do
        result
      else
        {:error, _} = result -> result
      end

    else
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `opts_filter_keys!/2` calls `opts_filter_keys/2` and if the result is `{:ok, opts}`, returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys!([:a, :b, :c])
      [a: 1, b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys!([b: :want_b, c: :and_c])
      [b: 2, c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys!(%{a: 42, b: nil})
      [a: 1, b: 2]

      iex> [a: 1, b: 2, c: 3] |> opts_filter_keys!(:not_a_key_spec)
      ** (ArgumentError) expected enum; got: :not_a_key_spec

      iex> :not_opts |> opts_filter_keys!([:a, :b, :c])
      ** (ArgumentError) expected valid derivable opts; got: :not_opts

  """

  @spec opts_filter_keys!(any, any) :: opts | no_return

  def opts_filter_keys!(opts, keys) do
    case opts_filter_keys(opts, keys) do
      {:ok, opts} -> opts
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_reject_keys/2` takes a *derivable opts* and a *key spec* and returns `{:ok, opts}` where `opts` has all keys from the original *derivable opts* that **do not** appear in the *key spec*.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys([:a, :b, :c])
      {:ok, []}

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys([b: "b value", c: :dont_want_this_key])
      {:ok, [a: 1]}

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys(%{a: nil, b: nil})
      {:ok, [c: 3]}

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys(:not_a_key_spec)
      {:error, %ArgumentError{message: "expected enum; got: :not_a_key_spec"}}

      iex> :not_opts |> opts_reject_keys([:a, :b, :c])
      {:error, %ArgumentError{message: "expected valid derivable opts; got: :not_opts"}}

  """

  @spec opts_reject_keys(any, any) :: {:ok, opts} | {:error, error}

  def opts_reject_keys(opts, keys)

  def opts_reject_keys(opts, keys) do

    with {:ok, reject_keys} <- keys |> normalise_key_spec do

      reject_map = reject_keys |> Map.new(fn k -> {k, nil} end)

      reject_pred = fn {k,_v} -> reject_map |> Map.has_key?(k) end

      with {:ok, _reject_opts} = result <- opts |> opts_reject(reject_pred) do
        result
      else
        {:error, _} = result -> result
      end

    else
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `opts_reject_keys!/2` calls `opts_reject_keys/2` and if the result is `{:ok, opts}`, returns `opts`.

  ## Examples

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys!([:a, :b, :c])
      []

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys!([b: "b value", c: :dont_want_this_key])
      [a: 1]

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys!(%{a: nil, b: nil})
      [c: 3]

      iex> [a: 1, b: 2, c: 3] |> opts_reject_keys!(:not_a_key_spec)
      ** (ArgumentError) expected enum; got: :not_a_key_spec

      iex> :not_opts |> opts_reject_keys!([:a, :b, :c])
      ** (ArgumentError) expected valid derivable opts; got: :not_opts

  """

  @spec opts_reject_keys!(any, any) :: opts | no_return

  def opts_reject_keys!(opts, keys) do
    case opts_reject_keys(opts, keys) do
      {:ok, opts} -> opts
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `opts_fetch_key_values/2` takes a *derivable opts* and a *key* and returns the values of the *key* as `{:ok, values}` where `values` will be a list.

  One of more indices can be provided to select the values at specific indices; the default is to return all values from `Keyword.get_values/2`.

  Note indices *must* be relative to the result of `Keyword.get_values/2` **not** the indices of the original *opts*

  Values are returned in the same order as the indices. Indices may be repeated. Indices are validated; asking for an unknown/impossible index will cause an error.

  ## Examples

  The default is to return *all* the values for a *key* i.e same as `Keyword.get_values/2`:

      iex> [a: 1, b: 2, c: 3] |> opts_fetch_key_values(:a)
      {:ok, [1]}

  This examples show multiple values being returned:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a)
      {:ok, [11, 12, 13]}

  Here the last value for the key is returned:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, -1)
      {:ok, [13]}

  Here only the first value is wanted:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, 0)
      {:ok, [11]}

  Values at different indices:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, [1,-1])
      {:ok, [12, 13]}

  Note order of the values is same order as the indices:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, [-2,0,-1])
      {:ok, [12, 11, 13]}

  The same index/indices can be repeated:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, [-2,0,-2,-1,0])
      {:ok, [12, 11, 12, 13, 11]}

  Indices are validated:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, 99)
      {:error, %ArgumentError{message: "index invalid; got: 99"}}

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values(:a, :not_an_index)
      {:error, %ArgumentError{message: "index invalid; got: :not_an_index"}}

  """

  @spec opts_fetch_key_values(any, any) :: {:ok, opts} | {:error, error}

  def opts_fetch_key_values(opts, key, indicies \\ nil)

  def opts_fetch_key_values(opts, key, nil) do

    with {:ok, norm_opts} <- opts |> opts_normalise,
         true <- norm_opts |> Keyword.has_key?(key) do
      {:ok, norm_opts |> Keyword.get_values(key)}
    else
      false -> new_key_error_result(key, opts)
    {:error, _} = result -> result
    end

  end

  def opts_fetch_key_values(opts, key, indices) do

    with {:ok, norm_opts} <- opts |> opts_normalise,
         true <- norm_opts |> Keyword.has_key?(key) do

      key_values = norm_opts |> Keyword.get_values(key)

      with {:ok, indices} <- key_values |> opts_indices_validate(indices) do

        indices
        |> List.wrap
        |> Enum.reduce({[],[]},
        fn index, {known_values,missing_indices} ->

          with {:ok, value} <- key_values |> Enum.fetch(index) do
            {[value | known_values], missing_indices}
          else
            :error -> {known_values, [index | missing_indices]}
          end

        end)
        |> case do

             {known_values, []} -> {:ok, known_values |> Enum.reverse}
             {_known_values, missing_indices} ->

               new_key_error_result(missing_indices, key_values)

           end

      else
        {:error, _} = result -> result
      end

    else
      false -> new_key_error_result(key, opts)
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `opts_fetch_key_values!/2` takes a *derivable opts* and a *key* and returns the values of the *key* as `{:ok, values}`.

  One of more indices can be provided to select the values at specific indices; the default is to return all values from `Keyword.get_values/2`.

  Note indices *must* be relative to the result of `Keyword.get_values/2` **not** the indices of the original *opts*

  Values are returned in the order they are given in the indices. Indices may be repeated.

  ## Examples

  The default is to return *all* the values for a *key*:

      iex> [a: 1, b: 2, c: 3] |> opts_fetch_key_values!(:a)
      [1]

  This examples show multiple values being returned:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a)
      [11, 12, 13]

  Here the last value for the key is returned:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a, -1)
      [13]

  Here the first value is wanted:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a, 0)
      [11]

  Values at different indices:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a, [1,-1])
      [12, 13]

  Note order of the values is same as order of the indices

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a, [-2,0,-1])
      [12, 11, 13]

  The same index/indices can be requested more than once:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a, [-2,0,-2,-1,0])
      [12, 11, 12, 13, 11]

  Indices are validated:

      iex> [a: 11, b: 2, a: 12, c: 3, a: 13] |> opts_fetch_key_values!(:a, :not_an_index)
      ** (ArgumentError) index invalid; got: :not_an_index

  """

  @spec opts_fetch_key_values!(any, any, any) :: list | no_return

  def opts_fetch_key_values!(opts, key, indices \\ nil)

  def opts_fetch_key_values!(opts, key, indices) do
    case opts_fetch_key_values(opts, key, indices) do
      {:ok, values} -> values
      {:error, error} -> raise error
    end

  end

  @doc ~S"""
  `canon_keys!/2` takes a *key list* together with a lookup dictionary and replaces each key with its canonical value from the dictionary. Unknown keys raise a `KeyError`.

  ## Examples

      iex> [:a, :b, :c] |> canon_keys!(%{a: 1, b: 2, c: 3})
      [1,2,3]

      iex> [:x] |> canon_keys!(%{a: 1, b: 2, c: 3})
      ** (KeyError) key :x not found in: %{a: 1, b: 2, c: 3}

  """

  @spec canon_keys!(alias_keys, dict) :: alias_keys | no_return

  def canon_keys!(keys, dict) when is_map(dict) do
    keys |> Enum.map(fn k -> dict |> Map.fetch!(k) end)
  end

  @doc ~S"""
  `canon_keys/2` takes a *key list* together with a lookup dictionary and replaces each key with its canonical value from the dictionary, returning `{:ok, canon_keys}`.

  If there are any unknown keys, `{:error, {canon_known_keys, unknown_keys}}` will be returned.

  ## Examples

      iex> [:a, :b, :c] |> canon_keys(%{a: 1, b: 2, c: 3})
      {:ok, [1,2,3]}

      iex> [:a, :x, :b, :y, :c, :z] |> canon_keys(%{a: 1, b: 2, c: 3})
      {:error, {[1, 2, 3], [:x, :y, :z]}}

  """

  @spec canon_keys(alias_keys, dict) :: {:ok, alias_keys} | {:error, error}

  def canon_keys(keys, dict) when is_map(dict) do

    keys
    # split into known and unknown keys
    |> Enum.split_with(fn k -> Map.has_key?(dict, k) end)
    |> case do

         # no unknown keys
         {known_keys, []} ->
           {:ok, known_keys |> canon_keys!(dict)}

         {known_keys, unknown_keys} ->
           {:error, {known_keys |> canon_keys!(dict), unknown_keys}}

       end

  end

  @doc ~S"""
  `canonical_keys/2` takes a *key list* and *key alias dict* and replaces each key with its canonical value from the dictionary, returning `{:ok, canonical_keys}`.

  If there are any unknown keys `{:error, error}`, where `error` is a `KeyError`, will be returned.

  ## Examples

      iex> [:a, :b, :c] |> canonical_keys(%{a: :p, b: :q, c: :r})
      {:ok, [:p,:q,:r]}

      iex> [:a, :b, :c] |> canonical_keys(%{a: 1, b: 2, c: 3})
      {:ok, [1,2,3]}

      iex> [:a, :x, :b, :y, :c, :z] |> canonical_keys(%{a: 1, b: 2, c: 3})
      {:error, %KeyError{key: [:x, :y, :z], term: %{a: 1, b: 2, c: 3}}}

  """

  @spec canonical_keys(alias_keys, any) :: {:ok, alias_keys} | {:error, error}

  def canonical_keys(keys, dict) do

    with {:ok, keys} <- keys |> normalise_key_list,
         {:ok, dict} <- dict |> normalise_key_dict do

      keys
      |> Enum.reject(fn k -> Map.has_key?(dict, k) end)
      |> case do

           # no unknown keys
           [] ->

             canon_keys = keys |> Enum.map(fn k -> dict |> Map.get(k) end)

             {:ok, canon_keys}

           unknown_keys ->

             unknown_keys |> new_key_error_result(dict)

         end
    else
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `canonical_keys!/2` calls `canonical_keys/2` and if the result is `{:ok, canonical_keys}` returns `canonical_keys`.

  ## Examples

      iex> [:a, :b, :c] |> canonical_keys!(%{a: :p, b: :q, c: :r})
      [:p,:q,:r]

      iex> [:a, :b, :c] |> canonical_keys!(%{a: 1, b: 2, c: 3})
      [1,2,3]

      iex> [:a, :x, :b, :y, :c, :z] |> canonical_keys!(%{a: 1, b: 2, c: 3})
      ** (KeyError) key [:x, :y, :z] not found in: %{a: 1, b: 2, c: 3}

  """

  @spec canonical_keys!(alias_keys, dict) :: alias_keys | no_return

  def canonical_keys!(keys, dict) do
    with {:ok, keys} <- keys |> canonical_keys(dict) do
      keys
    else
      {:error, error} -> raise error
    end
  end

  @doc ~S"""
  `canonical_key/2` takes a key together with a *key dict* and replaces the key with its canonical value from the dictionary, returning `{:ok, canonical_key}`.

  If the key is unknown, `{:error, error}`, `error` is a `KeyError`, will be returned.

  ## Examples

      iex> :b |> canonical_key(%{a: :p, b: :q, c: :r})
      {:ok, :q}

      iex> :a |> canonical_key(%{a: 1, b: 2, c: 3})
      {:ok, 1}

      iex> :x |> canonical_key(%{a: 1, b: 2, c: 3})
      {:error, %KeyError{key: :x, term: %{a: 1, b: 2, c: 3}}}

  """

  @spec canonical_key(alias_key, any) :: {:ok, alias_key} | {:error, error}

  def canonical_key(key, dict) do

    with {:ok, dict} <- dict |> normalise_key_dict,
         {:ok, keys} <- [key] |> canonical_keys(dict) do
      {:ok, keys |> hd}
    else
      {:error, %KeyError{} = error} -> {:error, error |> struct!(key: key)}
      {:error, _} = result -> result
    end

  end

  @doc ~S"""
  `canonical_key!/2` calls `canonical_key/2` and if the result is `{:ok, canonical_key}` returns `canonical_key`.

  ## Examples

      iex> :a |> canonical_key!(%{a: 1, b: 2, c: 3})
      1

      iex> :b |> canonical_key!(%{a: :p, b: :q, c: :r})
      :q

      iex> :x |> canonical_key!(%{a: 1, b: 2, c: 3})
      ** (KeyError) key :x not found in: %{a: 1, b: 2, c: 3}

  """

  @spec canonical_key!(alias_key, dict) :: alias_key | no_return

  def canonical_key!(key, dict) do
    with {:ok, key} <- key |> canonical_key(dict) do
      key
    else
      {:error, error} -> raise error
    end
  end

  @doc ~S"""

  `maybe_canon_keys/2` takes a *key list* together with a lookup dictionary and, if the key is in the dictionary, replaces it with its value. Unknown keys are passed through unchanged.

  ## Examples

      iex> [:a, :b, :c] |> maybe_canon_keys(%{a: 1, b: 2, c: 3})
      [1, 2, 3]

      iex> [:x, :a] |> maybe_canon_keys(%{a: 1, b: 2, c: 3})
      [:x, 1]

  """

  @spec maybe_canon_keys(alias_keys, dict) :: alias_keys

  def maybe_canon_keys(keys, dict) when is_map(dict) do
    keys
    |> Enum.map(fn k ->
      case dict |> Map.has_key?(k) do
        true -> dict |> Map.fetch!(k)
        _ -> k
      end
    end)
  end

  @doc ~S"""
  `list_wrap_flat_just/1` wraps a value (if not already a list), flattens and removes `nils` at the *first / top* level.

  ## Examples

      iex> [{:a, 1}, nil, [{:b1, 12}, nil, {:b2, [nil, 22, nil]}], nil, {:c, 3}] |> list_wrap_flat_just
      [a: 1, b1: 12, b2: [nil, 22, nil], c: 3]

      iex> [[[nil, 42, nil]]] |> list_wrap_flat_just
      [42]

  """

  @spec list_wrap_flat_just(any) :: [any]

  def list_wrap_flat_just(value) do
    value
    |> List.wrap
    |> List.flatten
    |> Enum.reject(&is_nil/1)
  end

  @doc ~S"""
  `list_wrap_flat_just_uniq/1` wraps a value (if not already a list), flattens, removes `nils` at
  the *first / top* level, and deletes duplicates (using `Enum.uniq/1`)

  ## Examples

      iex> [{:a, 1}, nil, [{:b1, 12}, nil, {:b2, [nil, 22, nil]}], nil, {:c, 3}, {:a, 1}, {:b1, 12}] |> list_wrap_flat_just_uniq
      [a: 1, b1: 12, b2: [nil, 22, nil], c: 3]

      iex> [nil, [42, [42, 42, nil]], 42] |> list_wrap_flat_just_uniq
      [42]

  """

  @spec list_wrap_flat_just_uniq(any) :: [any]

  def list_wrap_flat_just_uniq(value) do
    value
    |> List.wrap
    |> List.flatten
    |> Enum.reject(&is_nil/1)
    |> Enum.uniq
  end

  defp normalise_error_message(value)

  defp normalise_error_message(value) when is_binary(value) do
    value
  end

  defp normalise_error_message(value) when is_atom(value) do
    value |> to_string
  end

  defp normalise_error_message(value) do
    value |> inspect
  end

  defp normalise_error_value(value)

  defp normalise_error_value(value) do
    "got: #{value |> inspect}"
  end

  defp new_error_result(opts)

  defp new_error_result(opts) do

    message = [
      m: &normalise_error_message/1,
      v: &normalise_error_value/1,
    ]
    |> Enum.reduce([],fn {k,fun}, texts ->

      opts
      |> Keyword.has_key?(k)
      |> case do

           true ->

             text = opts |> Keyword.get(k) |> fun.()

             [text | texts]

           _ -> texts

         end

    end)
    |> Enum.reverse
    |> Enum.join("; ")

    {:error, %ArgumentError{message: message}}

  end

  defp new_key_error(values, term) do

    cond do
      Keyword.keyword?(values) -> values |> Keyword.keys
      is_list(values) -> values
      true -> raise ArgumentError, message: "expected opts or keys; got: #{inspect values}"
    end
    |> Enum.uniq
    |> case do
         [key] -> %KeyError{key: key, term: term}
         keys -> %KeyError{key: keys, term: term}
       end

  end

  defp new_key_error_result(values, term) do
    {:error, new_key_error(values, term)}
  end

end

