import { useEffect, useMemo, useState } from "react";
import type { Exercise } from "../engine/types";
import type { Answer } from "../engine/lesson";
import { mulberry32, shuffle } from "../engine/rng";

interface Props {
  exercise: Exercise;
  /** Called whenever the learner's current answer changes (null = incomplete). */
  onChange: (a: Answer | null) => void;
  /** After checking: show correctness. */
  revealed: boolean;
  seed: number;
}


export function ExerciseView({ exercise, onChange, revealed, seed }: Props) {
  switch (exercise.kind) {
    case "mc":
      return <MC ex={exercise} onChange={onChange} revealed={revealed} />;
    case "tf":
      return <TF ex={exercise} onChange={onChange} revealed={revealed} />;
    case "numeric":
    case "text":
      return <Typed ex={exercise} onChange={onChange} revealed={revealed} />;
    case "match":
      return <Match ex={exercise} onChange={onChange} revealed={revealed} seed={seed} />;
    case "order":
      return <Order ex={exercise} onChange={onChange} revealed={revealed} seed={seed} />;
    case "classify":
      return <Classify ex={exercise} onChange={onChange} revealed={revealed} seed={seed} />;
  }
}

function Context({ text }: { text?: string }) {
  return text ? <div className="context">{text}</div> : null;
}

/**
 * Keyboard selection for the click-one-option exercises. `keys` maps a
 * lowercased key name to the option it picks, so a choice can be reachable by
 * its number and, where it reads naturally, by a letter as well.
 *
 * Ignores presses while the answer is revealed, while a modifier is held, and
 * while the caret is in a field, so typing a numeric answer never triggers it.
 */
function useChoiceKeys(keys: Record<string, () => void>, active: boolean) {
  useEffect(() => {
    if (!active) return;
    const handler = (e: KeyboardEvent) => {
      if (e.metaKey || e.ctrlKey || e.altKey) return;
      const el = document.activeElement;
      const tag = el?.tagName;
      if (tag === "INPUT" || tag === "TEXTAREA" || (el as HTMLElement | null)?.isContentEditable) return;
      const pick = keys[e.key.toLowerCase()];
      if (!pick) return;
      e.preventDefault();
      pick();
    };
    window.addEventListener("keydown", handler);
    return () => window.removeEventListener("keydown", handler);
  }, [keys, active]);
}

function MC({ ex, onChange, revealed }: { ex: Extract<Exercise, { kind: "mc" }>; onChange: Props["onChange"]; revealed: boolean }) {
  const [sel, setSel] = useState<number | null>(null);
  useEffect(() => { setSel(null); onChange(null); }, [ex.id]); // eslint-disable-line react-hooks/exhaustive-deps
  const pickIdx = (i: number) => { if (revealed) return; setSel(i); onChange({ kind: "mc", index: i }); };
  const keys = useMemo(
    () => Object.fromEntries(ex.choices.map((_, i) => [String(i + 1), () => pickIdx(i)])),
    [ex.id, revealed], // eslint-disable-line react-hooks/exhaustive-deps
  );
  useChoiceKeys(keys, !revealed);
  return (
    <div>
      <Context text={ex.context} />
      <div className="prompt">{ex.prompt}</div>
      <div className="choices">
        {ex.choices.map((c, i) => {
          let cls = "choice";
          if (revealed) { if (c.correct) cls += " correct"; else if (sel === i) cls += " wrong"; }
          else if (sel === i) cls += " selected";
          return (
            <button key={i} className={cls} onClick={() => pickIdx(i)} disabled={revealed}>
              <span className="key">{i + 1}</span>
              <span>{c.text}</span>
            </button>
          );
        })}
      </div>
    </div>
  );
}

function TF({ ex, onChange, revealed }: { ex: Extract<Exercise, { kind: "tf" }>; onChange: Props["onChange"]; revealed: boolean }) {
  const [sel, setSel] = useState<boolean | null>(null);
  useEffect(() => { setSel(null); onChange(null); }, [ex.id]); // eslint-disable-line react-hooks/exhaustive-deps
  const pickV = (v: boolean) => { if (revealed) return; setSel(v); onChange({ kind: "tf", value: v }); };
  // Numbered like multiple choice, so 1 and 2 always mean "first" and "second".
  // T and F still work for anyone who reaches for them.
  const keys = useMemo(
    () => ({ "1": () => pickV(true), t: () => pickV(true), "2": () => pickV(false), f: () => pickV(false) }),
    [ex.id, revealed], // eslint-disable-line react-hooks/exhaustive-deps
  );
  useChoiceKeys(keys, !revealed);
  const cls = (v: boolean) => {
    let c = "choice";
    if (revealed) { if (v === ex.answer) c += " correct"; else if (sel === v) c += " wrong"; }
    else if (sel === v) c += " selected";
    return c;
  };
  return (
    <div>
      <Context text={ex.context} />
      <div className="muted small">True or false?</div>
      <div className="prompt">{ex.statement}</div>
      <div className="tf">
        <button className={cls(true)} onClick={() => pickV(true)} disabled={revealed}><span className="key">1</span> True</button>
        <button className={cls(false)} onClick={() => pickV(false)} disabled={revealed}><span className="key">2</span> False</button>
      </div>
    </div>
  );
}

function Typed({ ex, onChange, revealed }: { ex: Extract<Exercise, { kind: "numeric" | "text" }>; onChange: Props["onChange"]; revealed: boolean }) {
  const [val, setVal] = useState("");
  useEffect(() => { setVal(""); onChange(null); }, [ex.id]); // eslint-disable-line react-hooks/exhaustive-deps
  const update = (v: string) => {
    setVal(v);
    if (!v.trim()) return onChange(null);
    onChange(ex.kind === "numeric" ? { kind: "numeric", value: v } : { kind: "text", value: v });
  };
  return (
    <div>
      <Context text={ex.context} />
      <div className="prompt">{ex.prompt}</div>
      <div className="row">
        <input
          className="answer"
          autoFocus
          inputMode={ex.kind === "numeric" ? "decimal" : "text"}
          placeholder={ex.kind === "numeric" ? "Type a number (fractions like 3/8 and 25% are fine)" : "Type your answer"}
          value={val}
          onChange={(e) => update(e.target.value)}
          disabled={revealed}
        />
        {ex.kind === "numeric" && ex.unit ? <span className="unit-label">{ex.unit}</span> : null}
      </div>
    </div>
  );
}

function Match({ ex, onChange, revealed, seed }: { ex: Extract<Exercise, { kind: "match" }>; onChange: Props["onChange"]; revealed: boolean; seed: number }) {
  const rights = useMemo(() => shuffle(mulberry32(seed), ex.pairs.map((p) => p.right)), [ex.id, seed]); // eslint-disable-line react-hooks/exhaustive-deps
  const [pairs, setPairs] = useState<Record<string, string>>({});
  const [selLeft, setSelLeft] = useState<string | null>(null);
  useEffect(() => { setPairs({}); setSelLeft(null); onChange(null); }, [ex.id]); // eslint-disable-line react-hooks/exhaustive-deps
  const assign = (left: string, right: string) => {
    const next: Record<string, string> = { ...pairs };
    for (const k of Object.keys(next)) if (next[k] === right) delete next[k];
    next[left] = right;
    setPairs(next);
    setSelLeft(null);
    onChange(Object.keys(next).length === ex.pairs.length ? { kind: "match", pairs: next } : null);
  };
  const clickLeft = (l: string) => {
    if (revealed) return;
    if (pairs[l]) { const n = { ...pairs }; delete n[l]; setPairs(n); onChange(null); return; }
    setSelLeft(selLeft === l ? null : l);
  };
  const clickRight = (r: string) => {
    if (revealed || !selLeft) return;
    assign(selLeft, r);
  };
  const leftIndex = (l: string) => ex.pairs.findIndex((p) => p.left === l) + 1;
  const rightOwner = (r: string) => Object.keys(pairs).find((k) => pairs[k] === r);
  const correctFor = (l: string) => ex.pairs.find((p) => p.left === l)?.right;
  return (
    <div>
      <div className="prompt">{ex.prompt}</div>
      <div className="muted small" style={{ marginBottom: 8 }}>Tap an item on the left, then its match on the right.</div>
      <div className="match">
        <div className="col">
          {ex.pairs.map((p) => {
            let cls = "chip";
            if (revealed) cls += pairs[p.left] === p.right ? " paired" : " wrongpair";
            else if (selLeft === p.left) cls += " selected";
            else if (pairs[p.left]) cls += " paired";
            return (
              <button key={p.left} className={cls} onClick={() => clickLeft(p.left)} disabled={revealed}>
                <span className="tag">{leftIndex(p.left)}</span>{p.left}
              </button>
            );
          })}
        </div>
        <div className="col">
          {rights.map((r) => {
            const owner = rightOwner(r);
            let cls = "chip";
            if (revealed) cls += owner && correctFor(owner) === r ? " paired" : " wrongpair";
            else if (owner) cls += " paired";
            return (
              <button key={r} className={cls} onClick={() => clickRight(r)} disabled={revealed}>
                {owner ? <span className="tag">{leftIndex(owner)}</span> : null}{r}
              </button>
            );
          })}
        </div>
      </div>
    </div>
  );
}

function Order({ ex, onChange, revealed, seed }: { ex: Extract<Exercise, { kind: "order" }>; onChange: Props["onChange"]; revealed: boolean; seed: number }) {
  const bankInit = useMemo(() => {
    let s = shuffle(mulberry32(seed), ex.steps);
    if (s.every((v, i) => v === ex.steps[i]) && s.length > 1) s = [...s.slice(1), s[0]];
    return s;
  }, [ex.id, seed]); // eslint-disable-line react-hooks/exhaustive-deps
  const [chosen, setChosen] = useState<string[]>([]);
  useEffect(() => { setChosen([]); onChange(null); }, [ex.id]); // eslint-disable-line react-hooks/exhaustive-deps
  const bank = bankInit.filter((s) => !chosen.includes(s));
  const commit = (c: string[]) => { setChosen(c); onChange(c.length === ex.steps.length ? { kind: "order", steps: c } : null); };
  const move = (i: number, d: number) => {
    const c = [...chosen];
    const j = i + d;
    if (j < 0 || j >= c.length) return;
    [c[i], c[j]] = [c[j], c[i]];
    commit(c);
  };
  return (
    <div>
      <div className="prompt">{ex.prompt}</div>
      <div className="order-area">
        <div className="order-list">
          {chosen.length === 0 ? <div className="muted small center">Tap the steps below in the correct order.</div> : null}
          {chosen.map((s, i) => (
            <div key={s} className="order-item" style={revealed ? { borderColor: ex.steps[i] === s ? "var(--green)" : "var(--red)" } : undefined}>
              <span className="n">{i + 1}</span>
              <span>{s}</span>
              {!revealed ? (
                <span className="mv">
                  <button onClick={() => move(i, -1)} aria-label="move up">↑</button>
                  <button onClick={() => move(i, 1)} aria-label="move down">↓</button>
                  <button className="rm" onClick={() => commit(chosen.filter((x) => x !== s))} aria-label="remove">✕</button>
                </span>
              ) : null}
            </div>
          ))}
        </div>
        <div className="bank">
          {bank.map((s) => (
            <button key={s} className="chip" onClick={() => !revealed && commit([...chosen, s])} disabled={revealed}>{s}</button>
          ))}
        </div>
      </div>
    </div>
  );
}

function Classify({ ex, onChange, revealed, seed }: { ex: Extract<Exercise, { kind: "classify" }>; onChange: Props["onChange"]; revealed: boolean; seed: number }) {
  const items = useMemo(() => shuffle(mulberry32(seed), ex.items), [ex.id, seed]); // eslint-disable-line react-hooks/exhaustive-deps
  const [asg, setAsg] = useState<Record<string, string>>({});
  useEffect(() => { setAsg({}); onChange(null); }, [ex.id]); // eslint-disable-line react-hooks/exhaustive-deps
  const set = (t: string, c: string) => {
    if (revealed) return;
    const n = { ...asg, [t]: c };
    setAsg(n);
    onChange(Object.keys(n).length === ex.items.length ? { kind: "classify", assignment: n } : null);
  };
  return (
    <div>
      <div className="prompt">{ex.prompt}</div>
      <div className="classify">
        {items.map((it) => (
          <div key={it.text} className={"item" + (revealed ? (asg[it.text] === it.category ? " ok" : " bad") : "")}>
            <div className="txt">{it.text}</div>
            <div className="cats">
              {ex.categories.map((c) => (
                <button key={c} className={asg[it.text] === c ? "on" : ""} onClick={() => set(it.text, c)} disabled={revealed}>
                  {c}{revealed && it.category === c ? " ✓" : ""}
                </button>
              ))}
            </div>
          </div>
        ))}
      </div>
    </div>
  );
}
