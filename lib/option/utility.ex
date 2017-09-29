defmodule Plymio.Option.Utility do

  @moduledoc ~S"""
  Utility Function for Managing (Keyword) Options ("opts")
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

  defdelegate opts_take_keys(arg0,arg1), to: Keyword, as: :take
  defdelegate opts_drop_keys(arg0,arg1), to: Keyword, as: :drop

  @doc ~S"""
  `opts_create_aliases_tuples/1` takes `Keyword` where the keys are the canonical key names, and their values are zero (nil), one or more aliases for the canonical key.

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
  `opts_create_aliases_dict/1` does the same job as `opts_create_aliases_tuples/1` but returns a dictionary (map).

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
  `opts_create_defstruct/2` takes an opts list, together with a defaults map, and returns an opts list where each value is the value of the key in the defaults map (with default `nil`).

  `opts_create_defstruct/2` creates an argument suitable for use with `Kernel.defstruct/1`

  The defaults map must contain *only*  eys that are also in the opts list; any unknown keys will raise a `KeyError.`

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
  `opts_has_keys/2` takes an `opts` list, together with a list or dictionary (map) of wanted `keys`.

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
  `opts_has_keys?/2` call `opts_has_keys/2`.

  If the result is `{:ok, _}`, `true` is returned, else `false`.

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
  `opts_has_keys!/2` call `opts_has_keys/2`.

  If the result is `{:ok, opts}`, `opts` is returned, else a `KeyError` citing the missing keys is raised.

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
  `opts_canon_keys!/2` takes an opts list, together with a lookup dictionary and replaces each key with its canonical value from the dictionary. Unknown keys raise a `KeyError`.

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
  `opts_canon_keys/2` takes an opts list, together with either a dictionary (map) or (keyword) list of aliases.

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
  `opts_sort_keys/` takes an opts list, together with a list of sort keys, and returns the opts sorted in the sort keys order. Duplicate keys follow one after another.

  Any keys found but not given in the sort keys follow the sorted keys in the returned opts.

  Any key in the sort list not found in the opts is ignored.

  ## Examples

      iex> [a: 1, b: 2, c: 3, d: 4] |> opts_sort_keys([:c, :a])
      [c: 3, a: 1,  b: 2, d: 4]

      iex> [a: 1, b: 2, c: 3, d: 4] |> opts_sort_keys([:d, :x, :b, :z])
      [d: 4, b: 2, a: 1, c: 3]

  """

  @spec opts_sort_keys(opts, alias_keys) :: opts

  def opts_sort_keys(opts, keys \\ [])

  def opts_sort_keys([], _keys) do
    []
  end

  def opts_sort_keys(opts, []) do
    opts
  end

  def opts_sort_keys(opts, keys) do

    keys
    # add all the opts' keys to the sort order ones
    |> Kernel.++(Keyword.keys(opts))
    |> list_wrap_flat_just_uniq
    |> Enum.flat_map(fn k ->
      opts
      |> Keyword.get_values(k)
      |> Enum.map(fn v -> {k,v} end)
    end)

  end

  @doc ~S"""
  `opts_take_keys!/1` takes an opts list, together with a list of keys and returns the opts with just the supplied keys.

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

        # missing_keys = unknown_opts |> Keyword.keys |> Enum.uniq

        raise KeyError, key: missing_keys, term: opts

    end

  end

  @doc ~S"""
  `opts_drop_keys!/1` takes an opts list, together with a list of keys and returns the opts without the supplied keys.

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
  `canon_keys!/2` takes a list of keys together with a lookup dictionary and replaces each key with its canonical value from the dictionary. Unknown keys raise a `KeyError`.

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
  `canon_keys/2` takes a list of keys together with a lookup dictionary and replaces each key with its canonical value from the dictionary, returning `{:ok, known_keys_values}`.

  If there are any unknown keys, `{:error, {known_keys_values, unknown_keys}}` is returned.

  ## Examples

      iex> [:a, :b, :c] |> canon_keys(%{a: 1, b: 2, c: 3})
      {:ok, [1,2,3]}

      iex> [:a, :x, :b, :y, :c, :z] |> canon_keys(%{a: 1, b: 2, c: 3})
      {:error, {[1, 2, 3], [:x, :y, :z]}}

  """

  @spec canon_keys(alias_keys, dict) :: {:ok, alias_keys} | {:error, {alias_keys, list}}

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

  `maybe_canon_keys/2` takes a list of keys together with a lookup dictionary and, if the key is in the dictionary, replaces it with its value. Unknown keys are passed through unchanged.

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

end

