/- # mvcgen を使って命令的プログラムの検証をする

> 元記事:
> <https://hackmd.io/@sg-fro/BJRlurP_xg>

`mvcgen` タクティックはモナディックな検証条件生成器 (monadic verification condition generator) を実装しています。
このタクティックは Lean の命令的な `do` 記法で書かれたプログラムを含むゴールを、純粋な検証条件の集合に分解して処理します。
ここでいう検証条件 (verification condition) とは、`do` ブロックの背後にあるモナドを一切参照しない部分ゴールのことです。
つまり、プログラムの命令的な部分を抽象化し、最終的にモナドに依存しない純粋な性質を証明すれば、もとのゴール全体も成立する、という仕組みです。

mvcgen への「Hello world」として、次の例では `mySum` がローカルな可変変数と `for` ループを使って配列の総和を計算します。
そのうえで、この `mySum` が `Array.sum` と同値であることを証明します。
その際には、ループに対して不変条件 (invariant) を明示的に指定する必要があります。
-/
import Std.Tactic.Do

-- mvcgen はまだ使用しないでというwarningを消す
set_option mvcgen.warning false

/-- for文を使ってリストの和を計算する -/
def mySum (l : Array Nat) : Nat := Id.run do
  let mut out := 0
  for i in l do
    out := out + i
  return out

open Std.Do

theorem mySum_correct (l : Array Nat) : mySum l = l.sum := by
  -- モナディックに実装されている（`Id.run do ...`）部分にフォーカスします
  generalize h : mySum l = x
  apply Id.of_wp_run_eq h
  -- 検証条件に分解する
  mvcgen
  -- ループ全体を通して成り立たせたい不変条件を指定する
  -- * `out` は `let mut` で導入した変数の現在値を表します
  -- * `xs` は `List.Cursor` で，リストを接頭辞 `xs.prefix` と接尾辞 `xs.suffix` に
  --   分割して表すデータ構造です。どこまでループが進んだかを追跡します。
  --   つまり進捗（ループの到達位置）を記録します。
  -- 不変条件は「`out` が接頭辞の総和を保持している」ことです。
  -- 記法 ⌜p⌝ は，純粋な命題 `p : Prop` をアサーション言語に埋め込みます。
  case inv1 => exact ⇓⟨xs, out⟩ => ⌜xs.prefix.sum = out⌝
  -- 不変条件を指定した後は，“証明モードを抜ける”ことでゴールをさらに簡約できます。
  -- `mleave` は安定した `simp` サブセットに対する `simp only [...] at *` の糖衣です。
  all_goals mleave
  -- 各反復で不変条件が保存されることを証明する
  case vc1.step ih =>
    -- ここでのゴールには `pref` が現れます。これは不変条件に渡されたカーソルの
    -- `prefix` フィールドを束縛したものです。依存型のカーソルを展開すると
    -- `grind` が働きやすくなります。
    grind
  -- ループ開始時に不変条件が成り立つことを証明する
  case vc2.a.pre =>
    grind
  -- ループ終了時の不変条件から目標の性質が従うことを証明する
  case vc3.a.post h =>
    grind

/-
ループ不変条件を指定したあとは、証明は `all_goals mleave; grind` だけにまで短縮できます。
なお、`case` ラベルには `vc1`、`vc2`、`vc3` などの一意なプレフィックスが付きます。
ケースを参照するときは、このプレフィックスだけを使うべきで、サフィックスはその検証条件（VC）がどこから来たかをユーザーに伝えるための簡易な手掛かりに過ぎません。

例えば:

* **`vc1.step`** は、この検証条件がループにおける帰納ステップ（不変条件が次の繰り返しでも保持されること）を証明するものであることを示しています。
* **`vc2.a.pre1`** は、与えられたゴールの仮定が `forIn` の仕様における事前条件を満たすことを証明するものです。
* **`vc3.a.post`** は、`forIn` の仕様における事後条件からゴールが目標とする性質が導かれることを証明するものです。

`mvcgen`を使用しない伝統的な正しさ証明（correctness proof）と比較してみると役に立ちます。
-/

theorem mySum_correct_traditional (l : Array Nat) : mySum l = l.sum := by
  -- 配列をリストに変換する
  cases l with | mk l =>
  -- `mySum` を展開し，`forIn` を `foldl` に書き換える
  simp [mySum]
  -- 帰納法の仮定を一般化する
  suffices h : ∀ out, List.foldl (· + ·) out l = out + l.sum by simp [h]
  -- grind で片づける
  induction l with grind

/-
この証明は、`mvcgen` を用いた証明と同様に簡潔です。
しかし、従来型の手法はプログラムの重要な性質に依存しています：

* `for` ループが途中で `break` したり早期に `return` したりしないこと。そうでないと、`forIn` を `foldl` に書き換えることはできません。
* ループ本体 `(· + ·)` が、証明の中で繰り返し展開しても扱える程度に小さいこと。
* ループ本体が純粋 (pure) であり、すなわち副作用 (effects) を伴わないこと。
  （実際、基底モナド `Id` の計算はすべて `pure` を介して表せます。）

`forIn` は `foldlM` へ書き換えること自体は可能ですが、モナディックなループ本体について推論するのは `grind` にとって骨が折れる場合があります。

以下のセクションでは、`mvcgen` とそのサポートライブラリを学ぶためにいくつかの例を順に見ていき、あわせて従来型の証明が難しくなる場面も確認します。これはたいてい次の理由で生じます。

* 早期 `return` を伴う（ネストした）`for` ループなどの制御フロー構文を用いる `do` ブロック。
* `Id` 以外のモナドにおける効果的（effectful）な計算。そのような計算は暗黙のモナディック文脈（状態・例外など）に影響を与え，その影響をループ不変条件に反映する必要がある。

`mvcgen` は、これらの課題に対しても合理的な労力でスケールします。

-/
