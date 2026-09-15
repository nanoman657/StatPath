/**
 * Randomized exercise generators. Each returns a fresh Exercise so numeric
 * drills never repeat exactly. Explanations show the worked solution.
 */
import type { Exercise, Generator, MultipleChoice, Numeric } from "./types";
import { randInt, pick, shuffle } from "./rng";
import * as S from "./stats";

const f = S.fmt;

const gen = (id: string, make: Generator["make"]): Generator => ({ kind: "generator", id, make });

const numeric = (id: string, prompt: string, answer: number, explanation: string, extra: Partial<Numeric> = {}): Numeric => ({
  kind: "numeric",
  id,
  prompt,
  answer,
  explanation,
  ...extra,
});

const mc = (id: string, prompt: string, correct: string, wrong: string[], explanation: string, rng: () => number, context?: string): MultipleChoice => ({
  kind: "mc",
  id,
  prompt,
  choices: shuffle(rng, [{ text: correct, correct: true }, ...wrong.map((w) => ({ text: w }))]),
  explanation,
  context,
});

const dataset = (rng: () => number, n: number, lo: number, hi: number): number[] =>
  Array.from({ length: n }, () => randInt(rng, lo, hi));

const list = (xs: number[]) => xs.join(", ");

/* ---------- Chapter 1: sampling ---------- */

export const sampleVsPopulation = gen("g.sample-or-population", (rng) => {
  const scenarios = [
    { s: "A nurse records the blood pressure of every patient admitted to a hospital in one year and reports the average for that hospital.", stat: "statistic", group: "the patients admitted that year" },
    { s: "A pollster calls 1,200 registered voters and finds that 52% support a ballot measure.", stat: "statistic", group: "1,200 voters" },
    { s: "A census counts every resident of a town; 38% are under 18.", stat: "parameter", group: "all residents" },
    { s: "A quality engineer tests 50 light bulbs from a day's production and finds a mean life of 1,020 hours.", stat: "statistic", group: "50 bulbs" },
    { s: "The registrar reports that the mean GPA of all 8,000 enrolled students is 3.1.", stat: "parameter", group: "all enrolled students" },
  ];
  const sc = pick(rng, scenarios);
  const isParam = sc.stat === "parameter";
  return mc(
    "g.sample-or-population",
    "Is the reported number a statistic or a parameter?",
    isParam ? "A parameter (it describes the whole population)" : "A statistic (it describes a sample)",
    isParam ? ["A statistic (it describes a sample)"] : ["A parameter (it describes the whole population)"],
    isParam
      ? `Every member of the population (${sc.group}) was measured, so the number describes the population and is a parameter.`
      : `Only a subset (${sc.group}) was measured, so the number describes a sample and is a statistic.`,
    rng,
    sc.s,
  );
});

export const samplingMethod = gen("g.sampling-method", (rng) => {
  const items = [
    { s: "Number every student 1 to 500 and use a random number generator to select 40.", a: "Simple random" },
    { s: "Divide employees into departments, then randomly select 5 people from each department.", a: "Stratified" },
    { s: "Randomly choose 6 of the 40 classrooms in a school and survey every student in those classrooms.", a: "Cluster" },
    { s: "Start at a random position on an alphabetical customer list and take every 20th name.", a: "Systematic" },
    { s: "Survey the first 30 shoppers who walk into a store on Saturday morning.", a: "Convenience" },
    { s: "Ask people who volunteer to respond to an online poll on a news site.", a: "Convenience" },
  ];
  const it = pick(rng, items);
  const all = ["Simple random", "Stratified", "Cluster", "Systematic", "Convenience"];
  return mc(
    "g.sampling-method",
    "Which sampling method is being used?",
    it.a,
    shuffle(rng, all.filter((x) => x !== it.a)).slice(0, 3),
    `This is ${it.a.toLowerCase()} sampling. Stratified = some from every group; cluster = all from some groups; systematic = every kth; simple random = every sample of size n equally likely; convenience = whoever is easy to reach (and not random).`,
    rng,
    it.s,
  );
});

export const relativeFrequency = gen("g.relative-frequency", (rng) => {
  const counts = [randInt(rng, 3, 12), randInt(rng, 3, 12), randInt(rng, 3, 12), randInt(rng, 3, 12)];
  const total = counts.reduce((a, b) => a + b, 0);
  const cats = ["A", "B", "C", "D"];
  const i = randInt(rng, 0, 3);
  const cum = counts.slice(0, i + 1).reduce((a, b) => a + b, 0);
  const askCum = rng() < 0.4;
  const table = cats.map((c, k) => `${c}: ${counts[k]}`).join(" | ");
  return numeric(
    "g.relative-frequency",
    askCum
      ? `What is the cumulative relative frequency through category ${cats[i]}? (Round to 4 decimal places.)`
      : `What is the relative frequency of category ${cats[i]}? (Round to 4 decimal places.)`,
    askCum ? S.round(cum / total, 4) : S.round(counts[i] / total, 4),
    askCum
      ? `Cumulative frequency through ${cats[i]} = ${cum}. Divide by the total ${total}: ${cum}/${total} = ${f(cum / total, 4)}.`
      : `Relative frequency = frequency ÷ total = ${counts[i]}/${total} = ${f(counts[i] / total, 4)}.`,
    { context: `Frequency table (n = ${total}): ${table}`, tolerance: 0.001 },
  );
});

/* ---------- Chapter 2: descriptive statistics ---------- */

export const meanOfData = gen("g.mean", (rng) => {
  const xs = dataset(rng, randInt(rng, 5, 8), 1, 30);
  const m = S.mean(xs);
  return numeric("g.mean", "Find the sample mean x̄. (Round to 2 decimals.)", S.round(m, 2), `Add the values (${xs.reduce((a, b) => a + b, 0)}) and divide by n = ${xs.length}: x̄ = ${f(m)}.`, { context: `Data: ${list(xs)}`, tolerance: 0.011 });
});

export const medianOfData = gen("g.median", (rng) => {
  const xs = dataset(rng, randInt(rng, 5, 9), 1, 40);
  const med = S.median(xs);
  const sorted = [...xs].sort((a, b) => a - b);
  return numeric("g.median", "Find the median.", med, `Sort the data: ${list(sorted)}. With n = ${xs.length}, the median is the middle value${xs.length % 2 ? "" : " (average of the two middle values)"}: ${f(med)}.`, { context: `Data: ${list(xs)}`, tolerance: 0.011 });
});

export const modeOfData = gen("g.mode", (rng) => {
  const base = dataset(rng, 5, 1, 9);
  const repeated = pick(rng, base);
  const xs = shuffle(rng, [...base, repeated, repeated]);
  const modes = S.mode(xs);
  return numeric("g.mode", "What is the mode of the data set?", modes[0], `The value that appears most often is ${modes[0]}.`, { context: `Data: ${list(xs)}`, tolerance: 0 });
});

export const sampleSDOfData = gen("g.sample-sd", (rng) => {
  const xs = dataset(rng, randInt(rng, 5, 7), 2, 20);
  const sd = S.sampleSD(xs);
  const m = S.mean(xs);
  return numeric("g.sample-sd", "Find the sample standard deviation s. (Round to 2 decimals.)", S.round(sd, 2), `x̄ = ${f(m)}. Sum of squared deviations = ${f(S.sampleVariance(xs) * (xs.length - 1), 2)}. Divide by n − 1 = ${xs.length - 1} to get s² = ${f(S.sampleVariance(xs), 3)}, so s = √s² = ${f(sd)}.`, { context: `Sample data: ${list(xs)}`, tolerance: 0.02 });
});

export const zScoreFromData = gen("g.zscore", (rng) => {
  const mu = randInt(rng, 40, 120);
  const sigma = randInt(rng, 4, 15);
  const x = mu + randInt(rng, -3, 3) * sigma + randInt(rng, -4, 4);
  const z = (x - mu) / sigma;
  return numeric("g.zscore", `A value is x = ${x}. What is its z-score? (Round to 2 decimals.)`, S.round(z, 2), `z = (x − μ)/σ = (${x} − ${mu})/${sigma} = ${f(z)}. A z-score counts how many standard deviations x sits from the mean.`, { context: `Population mean μ = ${mu}, standard deviation σ = ${sigma}.`, tolerance: 0.011 });
});

export const valueFromZ = gen("g.value-from-z", (rng) => {
  const mu = randInt(rng, 50, 100);
  const sigma = randInt(rng, 3, 12);
  const z = pick(rng, [-2.5, -2, -1.5, -1, -0.5, 0.5, 1, 1.5, 2, 2.5]);
  const x = mu + z * sigma;
  return numeric("g.value-from-z", `Which data value has a z-score of ${z}?`, x, `x = μ + zσ = ${mu} + (${z})(${sigma}) = ${f(x)}.`, { context: `Mean μ = ${mu}, standard deviation σ = ${sigma}.`, tolerance: 0.011 });
});

export const quartilesIQR = gen("g.iqr", (rng) => {
  const xs = dataset(rng, pick(rng, [8, 9, 10, 11, 12]), 1, 50);
  const q = S.quartiles(xs);
  const sorted = [...xs].sort((a, b) => a - b);
  const which = pick(rng, ["q1", "q3", "iqr"] as const);
  const label = { q1: "first quartile Q₁", q3: "third quartile Q₃", iqr: "interquartile range (IQR)" }[which];
  return numeric("g.iqr", `Find the ${label}.`, q[which], `Sorted: ${list(sorted)}. Median = ${f(q.q2)}. Q₁ is the median of the lower half = ${f(q.q1)}; Q₃ is the median of the upper half = ${f(q.q3)}; IQR = Q₃ − Q₁ = ${f(q.iqr)}.`, { context: `Data: ${list(xs)}`, tolerance: 0.011 });
});

export const outlierFence = gen("g.outlier-fence", (rng) => {
  const q1 = randInt(rng, 10, 40);
  const iqr = randInt(rng, 5, 20);
  const q3 = q1 + iqr;
  const upper = rng() < 0.5;
  const ans = upper ? q3 + 1.5 * iqr : q1 - 1.5 * iqr;
  return numeric("g.outlier-fence", `Using the 1.5·IQR rule, any value ${upper ? "above" : "below"} what number is a potential outlier?`, ans, `IQR = Q₃ − Q₁ = ${q3} − ${q1} = ${iqr}. ${upper ? `Upper fence = Q₃ + 1.5·IQR = ${q3} + ${1.5 * iqr} = ${ans}` : `Lower fence = Q₁ − 1.5·IQR = ${q1} − ${1.5 * iqr} = ${ans}`}.`, { context: `Q₁ = ${q1}, Q₃ = ${q3}`, tolerance: 0.011 });
});

export const percentileInterpretation = gen("g.percentile", (rng) => {
  const p = pick(rng, [20, 30, 40, 60, 70, 80, 90]);
  const thing = pick(rng, ["a test score", "a runner's finishing time", "a house price", "a commute time"]);
  const lowerIsBetter = thing.includes("time");
  return mc(
    "g.percentile",
    `${thing[0].toUpperCase() + thing.slice(1)} is at the ${p}th percentile. What does that mean?`,
    `${p}% of the values are at or below it, and ${100 - p}% are at or above it`,
    [`${p}% of the values are above it`, `The value equals ${p}% of the maximum`, `It is ${p} standard deviations above the mean`],
    `The kth percentile splits the data so that about k% of values are at or below it.${lowerIsBetter ? " For times, being at a low percentile is good (faster than most)." : ""}`,
    rng,
  );
});

/* ---------- Chapter 3: probability ---------- */

export const basicProbability = gen("g.basic-prob", (rng) => {
  const kind = pick(rng, ["die", "cards", "marbles"] as const);
  if (kind === "die") {
    const target = pick(rng, [{ t: "an even number", n: 3 }, { t: "a number greater than 4", n: 2 }, { t: "a number less than 3", n: 2 }, { t: "a multiple of 3", n: 2 }, { t: "a 5", n: 1 }]);
    return numeric("g.basic-prob", `A fair six-sided die is rolled once. What is P(${target.t})? (Enter a decimal, 4 places.)`, S.round(target.n / 6, 4), `${target.n} of the 6 equally likely outcomes qualify: ${target.n}/6 = ${f(target.n / 6, 4)}.`, { tolerance: 0.001 });
  }
  if (kind === "cards") {
    const target = pick(rng, [{ t: "a heart", n: 13 }, { t: "a face card (J, Q, K)", n: 12 }, { t: "an ace", n: 4 }, { t: "a red card", n: 26 }, { t: "a black king", n: 2 }]);
    return numeric("g.basic-prob", `One card is drawn from a standard 52-card deck. What is P(${target.t})? (4 decimals.)`, S.round(target.n / 52, 4), `${target.n} of 52 cards qualify: ${target.n}/52 = ${f(target.n / 52, 4)}.`, { tolerance: 0.001 });
  }
  const r = randInt(rng, 2, 8), b = randInt(rng, 2, 8), g = randInt(rng, 1, 6);
  const total = r + b + g;
  const which = pick(rng, [["red", r], ["blue", b], ["green", g]] as const);
  return numeric("g.basic-prob", `What is the probability that one marble drawn at random is ${which[0]}? (4 decimals.)`, S.round(which[1] / total, 4), `${which[1]} ${which[0]} marbles out of ${total} total: ${which[1]}/${total} = ${f(which[1] / total, 4)}.`, { context: `A bag holds ${r} red, ${b} blue, and ${g} green marbles.`, tolerance: 0.001 });
});

export const complementRule = gen("g.complement", (rng) => {
  const p = randInt(rng, 5, 95) / 100;
  return numeric("g.complement", `If P(A) = ${p}, what is P(A′), the probability of the complement of A?`, S.round(1 - p, 2), `P(A′) = 1 − P(A) = 1 − ${p} = ${f(1 - p)}.`, { tolerance: 0.006 });
});

export const additionRule = gen("g.addition-rule", (rng) => {
  const pa = randInt(rng, 20, 60) / 100;
  const pb = randInt(rng, 20, 60) / 100;
  const pab = S.round(Math.min(pa, pb) * randInt(rng, 2, 8) / 10, 2);
  const ans = pa + pb - pab;
  return numeric("g.addition-rule", "Find P(A OR B). (2 decimals.)", S.round(ans, 2), `P(A OR B) = P(A) + P(B) − P(A AND B) = ${pa} + ${pb} − ${pab} = ${f(ans)}.`, { context: `P(A) = ${pa}, P(B) = ${pb}, P(A AND B) = ${pab}`, tolerance: 0.006 });
});

export const conditionalProbability = gen("g.conditional", (rng) => {
  const pb = randInt(rng, 30, 80) / 100;
  const pab = S.round(pb * randInt(rng, 2, 9) / 10, 2);
  const ans = pab / pb;
  return numeric("g.conditional", "Find P(A | B). (Round to 3 decimals.)", S.round(ans, 3), `P(A|B) = P(A AND B) / P(B) = ${pab} / ${pb} = ${f(ans, 3)}.`, { context: `P(A AND B) = ${pab}, P(B) = ${pb}`, tolerance: 0.002 });
});

export const independenceCheck = gen("g.independence", (rng) => {
  const pa = randInt(rng, 2, 8) / 10;
  const pb = randInt(rng, 2, 8) / 10;
  const indep = rng() < 0.5;
  const pab = indep ? S.round(pa * pb, 2) : S.round(pa * pb + pick(rng, [-0.1, 0.1, 0.15]), 2);
  return mc(
    "g.independence",
    "Are events A and B independent?",
    indep ? "Yes, because P(A AND B) = P(A)·P(B)" : "No, because P(A AND B) ≠ P(A)·P(B)",
    indep ? ["No, because P(A AND B) ≠ P(A)·P(B)", "Yes, because P(A AND B) > 0", "No, because A and B are mutually exclusive"] : ["Yes, because P(A AND B) = P(A)·P(B)", "Yes, because P(A AND B) > 0", "No, because A and B are mutually exclusive"],
    `Independent means P(A AND B) = P(A)P(B). Here P(A)P(B) = ${pa}×${pb} = ${f(pa * pb, 2)}${indep ? " which matches P(A AND B), so they are independent." : ` which differs from P(A AND B) = ${pab}, so they are dependent.`}`,
    rng,
    `P(A) = ${pa}, P(B) = ${pb}, P(A AND B) = ${pab}`,
  );
});

export const contingencyTable = gen("g.contingency", (rng) => {
  const a = randInt(rng, 10, 40), b = randInt(rng, 10, 40), c = randInt(rng, 10, 40), d = randInt(rng, 10, 40);
  const n = a + b + c + d;
  const ctx = `Survey of ${n} people:\n            Coffee | Tea\n  Morning     ${a}   | ${b}\n  Evening     ${c}   | ${d}`;
  const q = pick(rng, [
    { p: "P(Coffee)", v: (a + c) / n, e: `Coffee column total ${a + c} out of ${n}.` },
    { p: "P(Morning AND Tea)", v: b / n, e: `The Morning/Tea cell is ${b} out of ${n}.` },
    { p: "P(Coffee | Evening)", v: c / (c + d), e: `Restrict to the Evening row (${c + d} people); ${c} chose coffee.` },
    { p: "P(Morning | Tea)", v: b / (b + d), e: `Restrict to the Tea column (${b + d} people); ${b} are Morning.` },
    { p: "P(Morning OR Coffee)", v: (a + b + c) / n, e: `Morning row (${a + b}) + Coffee column (${a + c}) − overlap (${a}) = ${a + b + c}, out of ${n}.` },
  ]);
  return numeric("g.contingency", `Find ${q.p}. (Round to 3 decimals.)`, S.round(q.v, 3), `${q.e} Probability = ${f(q.v, 3)}.`, { context: ctx, tolerance: 0.002 });
});

/* ---------- Chapter 4: discrete random variables ---------- */

export const expectedValue = gen("g.expected-value", (rng) => {
  const xs = [0, 1, 2, 3];
  let w = [randInt(rng, 1, 5), randInt(rng, 1, 5), randInt(rng, 1, 5), randInt(rng, 1, 5)];
  const tot = w.reduce((a, b) => a + b, 0);
  const ps = w.map((v) => S.round(v / tot, 2));
  // fix rounding so probabilities sum to 1
  ps[3] = S.round(1 - ps[0] - ps[1] - ps[2], 2);
  const mu = xs.reduce((acc, x, i) => acc + x * ps[i], 0);
  const table = xs.map((x, i) => `x=${x}: P=${ps[i]}`).join(" | ");
  return numeric("g.expected-value", "Find the expected value μ = Σ x·P(x). (2 decimals.)", S.round(mu, 2), `μ = ${xs.map((x, i) => `${x}(${ps[i]})`).join(" + ")} = ${f(mu)}.`, { context: `Probability distribution: ${table}`, tolerance: 0.011 });
});

export const binomialProbability = gen("g.binomial", (rng) => {
  const n = randInt(rng, 5, 15);
  const p = pick(rng, [0.1, 0.2, 0.25, 0.3, 0.4, 0.5, 0.6, 0.7, 0.75, 0.8]);
  const x = randInt(rng, 0, n);
  const mode = pick(rng, ["exact", "atmost", "atleast"] as const);
  const exact = S.binomialPMF(n, p, x);
  const cdf = S.binomialCDF(n, p, x);
  const v = mode === "exact" ? exact : mode === "atmost" ? cdf : 1 - S.binomialCDF(n, p, x - 1);
  const label = mode === "exact" ? `P(X = ${x})` : mode === "atmost" ? `P(X ≤ ${x})` : `P(X ≥ ${x})`;
  const exp = mode === "exact"
    ? `P(X = ${x}) = C(${n},${x}) p^${x} (1−p)^${n - x} = ${S.choose(n, x)} × ${p}^${x} × ${f(1 - p)}^${n - x} = ${f(v, 4)}.`
    : mode === "atmost"
      ? `Add P(X = 0) through P(X = ${x}) (calculator: binomcdf(${n}, ${p}, ${x})) = ${f(v, 4)}.`
      : `P(X ≥ ${x}) = 1 − P(X ≤ ${x - 1}) = 1 − binomcdf(${n}, ${p}, ${x - 1}) = ${f(v, 4)}.`;
  return numeric("g.binomial", `X ~ B(${n}, ${p}). Find ${label}. (4 decimals.)`, S.round(v, 4), exp, { tolerance: 0.001 });
});

export const binomialMeanSD = gen("g.binomial-mean-sd", (rng) => {
  const n = randInt(rng, 10, 200);
  const p = pick(rng, [0.1, 0.15, 0.2, 0.25, 0.3, 0.4, 0.5, 0.6, 0.75, 0.8, 0.9]);
  const askSD = rng() < 0.5;
  const mu = n * p, sd = Math.sqrt(n * p * (1 - p));
  return numeric("g.binomial-mean-sd", askSD ? `X ~ B(${n}, ${p}). Find the standard deviation σ. (2 decimals.)` : `X ~ B(${n}, ${p}). Find the mean μ.`, askSD ? S.round(sd, 2) : S.round(mu, 2), askSD ? `σ = √(npq) = √(${n}·${p}·${f(1 - p)}) = ${f(sd)}.` : `μ = np = ${n}·${p} = ${f(mu)}.`, { tolerance: 0.011 });
});

export const geometricProbability = gen("g.geometric", (rng) => {
  const p = pick(rng, [0.1, 0.2, 0.25, 0.3, 0.4, 0.5]);
  const x = randInt(rng, 1, 6);
  const v = S.geometricPMF(p, x);
  return numeric("g.geometric", `Each trial succeeds with probability p = ${p}. Find the probability that the first success occurs on trial ${x}. (4 decimals.)`, S.round(v, 4), `Geometric: P(X = ${x}) = (1−p)^${x - 1}·p = ${f(1 - p)}^${x - 1} × ${p} = ${f(v, 4)}. The mean number of trials is 1/p = ${f(1 / p)}.`, { tolerance: 0.001 });
});

export const poissonProbability = gen("g.poisson", (rng) => {
  const mu = pick(rng, [1, 1.5, 2, 2.5, 3, 4, 5]);
  const x = randInt(rng, 0, 6);
  const atMost = rng() < 0.4;
  const v = atMost ? S.poissonCDF(mu, x) : S.poissonPMF(mu, x);
  return numeric("g.poisson", `X ~ Poisson(${mu}). Find ${atMost ? `P(X ≤ ${x})` : `P(X = ${x})`}. (4 decimals.)`, S.round(v, 4), atMost ? `Sum P(X = k) = e^−μ μ^k / k! for k = 0…${x} (poissoncdf(${mu}, ${x})) = ${f(v, 4)}.` : `P(X = ${x}) = e^−${mu} · ${mu}^${x} / ${x}! = ${f(v, 4)}.`, { tolerance: 0.001 });
});

export const hypergeometric = gen("g.hypergeometric", (rng) => {
  const r = randInt(rng, 4, 8), b = randInt(rng, 4, 8), n = randInt(rng, 3, 5);
  const N = r + b;
  const x = randInt(rng, 1, Math.min(n, r));
  const v = S.hypergeometricPMF(N, r, n, x);
  return numeric("g.hypergeometric", `A committee of ${n} is chosen at random without replacement from ${r} faculty and ${b} students. Find the probability exactly ${x} faculty are chosen. (4 decimals.)`, S.round(v, 4), `Hypergeometric: [C(${r},${x})·C(${b},${n - x})] / C(${N},${n}) = [${S.choose(r, x)}·${S.choose(b, n - x)}] / ${S.choose(N, n)} = ${f(v, 4)}.`, { tolerance: 0.001 });
});

/* ---------- Chapter 5: continuous ---------- */

export const uniformProbability = gen("g.uniform", (rng) => {
  const a = randInt(rng, 0, 10);
  const b = a + randInt(rng, 5, 30);
  const lo = a + randInt(rng, 0, Math.floor((b - a) / 2));
  const hi = lo + randInt(rng, 1, b - lo);
  const v = (hi - lo) / (b - a);
  const q = pick(rng, ["prob", "mean", "sd"] as const);
  if (q === "mean") return numeric("g.uniform", `X ~ U(${a}, ${b}). Find the mean μ.`, S.round((a + b) / 2, 2), `μ = (a + b)/2 = (${a} + ${b})/2 = ${f((a + b) / 2)}.`, { tolerance: 0.011 });
  if (q === "sd") return numeric("g.uniform", `X ~ U(${a}, ${b}). Find the standard deviation σ. (2 decimals.)`, S.round((b - a) / Math.sqrt(12), 2), `σ = (b − a)/√12 = ${b - a}/3.4641 = ${f((b - a) / Math.sqrt(12))}.`, { tolerance: 0.011 });
  return numeric("g.uniform", `X ~ U(${a}, ${b}). Find P(${lo} < X < ${hi}). (4 decimals.)`, S.round(v, 4), `For a uniform distribution, probability = (width of interval) × (height 1/(b−a)) = (${hi} − ${lo}) × 1/${b - a} = ${f(v, 4)}.`, { tolerance: 0.001 });
});

export const exponentialProbability = gen("g.exponential", (rng) => {
  const muVal = pick(rng, [2, 4, 5, 8, 10, 12, 15, 20]);
  const m = 1 / muVal;
  const x = randInt(rng, 1, 2 * muVal);
  const less = rng() < 0.5;
  const v = less ? S.exponentialCDF(x, m) : 1 - S.exponentialCDF(x, m);
  return numeric("g.exponential", `The time between arrivals is exponential with mean ${muVal} minutes. Find P(X ${less ? "<" : ">"} ${x}). (4 decimals.)`, S.round(v, 4), `Decay rate m = 1/μ = ${f(m, 4)}. ${less ? `P(X < x) = 1 − e^(−mx) = 1 − e^(−${f(m, 4)}·${x}) = ${f(v, 4)}.` : `P(X > x) = e^(−mx) = e^(−${f(m, 4)}·${x}) = ${f(v, 4)}.`}`, { tolerance: 0.001 });
});

/* ---------- Chapter 6: normal ---------- */

export const normalProbability = gen("g.normal-prob", (rng) => {
  const mu = randInt(rng, 50, 100);
  const sigma = randInt(rng, 5, 15);
  const kind = pick(rng, ["less", "greater", "between"] as const);
  const x1 = mu + randInt(rng, -20, 20);
  const x2 = x1 + randInt(rng, 3, 20);
  let v: number, label: string, exp: string;
  const z1 = (x1 - mu) / sigma;
  const z2 = (x2 - mu) / sigma;
  if (kind === "less") { v = S.normalCDF(z1); label = `P(X < ${x1})`; exp = `z = (${x1} − ${mu})/${sigma} = ${f(z1)}. P(Z < ${f(z1)}) = ${f(v, 4)} (normalcdf(−1E99, ${x1}, ${mu}, ${sigma})).`; }
  else if (kind === "greater") { v = 1 - S.normalCDF(z1); label = `P(X > ${x1})`; exp = `z = ${f(z1)}. P(Z > ${f(z1)}) = 1 − ${f(S.normalCDF(z1), 4)} = ${f(v, 4)}.`; }
  else { v = S.normalCDF(z2) - S.normalCDF(z1); label = `P(${x1} < X < ${x2})`; exp = `z-scores ${f(z1)} and ${f(z2)}. Area between = ${f(S.normalCDF(z2), 4)} − ${f(S.normalCDF(z1), 4)} = ${f(v, 4)}.`; }
  return numeric("g.normal-prob", `X ~ N(${mu}, ${sigma}). Find ${label}. (4 decimals.)`, S.round(v, 4), exp, { tolerance: 0.002 });
});

export const normalInverse = gen("g.normal-inv", (rng) => {
  const mu = randInt(rng, 50, 100);
  const sigma = randInt(rng, 5, 15);
  const p = pick(rng, [0.05, 0.1, 0.2, 0.25, 0.3, 0.4, 0.6, 0.7, 0.75, 0.8, 0.9, 0.95]);
  const z = S.normalInv(p);
  const x = mu + z * sigma;
  return numeric("g.normal-inv", `X ~ N(${mu}, ${sigma}). Find the ${Math.round(p * 100)}th percentile, the value k with P(X < k) = ${p}. (1 decimal.)`, S.round(x, 1), `invNorm(${p}) = ${f(z, 3)}. k = μ + zσ = ${mu} + (${f(z, 3)})(${sigma}) = ${f(x, 1)}.`, { tolerance: 0.3 });
});

export const empiricalRule = gen("g.empirical-rule", (rng) => {
  const mu = randInt(rng, 40, 100);
  const sigma = randInt(rng, 3, 12);
  const k = pick(rng, [1, 2, 3]);
  const pct = { 1: 68, 2: 95, 3: 99.7 }[k];
  const lo = mu - k * sigma, hi = mu + k * sigma;
  return mc("g.empirical-rule", `X is approximately normal with μ = ${mu} and σ = ${sigma}. About what percent of values fall between ${lo} and ${hi}?`, `${pct}%`, ["50%", "68%", "95%", "99.7%", "34%"].filter((s) => s !== `${pct}%`).slice(0, 3), `${lo} and ${hi} are ${k} standard deviation${k > 1 ? "s" : ""} from the mean. The Empirical Rule: about 68% within 1σ, 95% within 2σ, 99.7% within 3σ.`, rng);
});

/* ---------- Chapter 7: CLT ---------- */

export const cltMeans = gen("g.clt-means", (rng) => {
  const mu = randInt(rng, 40, 120);
  const sigma = randInt(rng, 6, 20);
  const n = pick(rng, [25, 36, 49, 64, 100]);
  const se = sigma / Math.sqrt(n);
  const q = pick(rng, ["se", "prob"] as const);
  if (q === "se") return numeric("g.clt-means", `A population has μ = ${mu}, σ = ${sigma}. For samples of size n = ${n}, what is the standard deviation of the sample mean X̄ (the standard error)? (3 decimals.)`, S.round(se, 3), `σ_x̄ = σ/√n = ${sigma}/√${n} = ${sigma}/${f(Math.sqrt(n), 2)} = ${f(se, 3)}.`, { tolerance: 0.002 });
  const x = mu + pick(rng, [-2, -1.5, -1, 1, 1.5, 2]) * se;
  const gt = rng() < 0.5;
  const z = (x - mu) / se;
  const v = gt ? 1 - S.normalCDF(z) : S.normalCDF(z);
  return numeric("g.clt-means", `A population has μ = ${mu}, σ = ${sigma}. A random sample of n = ${n} is drawn. Find P(X̄ ${gt ? ">" : "<"} ${f(x, 2)}). (4 decimals.)`, S.round(v, 4), `By the CLT, X̄ ~ N(${mu}, ${sigma}/√${n} = ${f(se, 3)}). z = (${f(x, 2)} − ${mu})/${f(se, 3)} = ${f(z, 2)}. ${gt ? "Right-tail" : "Left-tail"} area = ${f(v, 4)}.`, { tolerance: 0.002 });
});

export const cltSums = gen("g.clt-sums", (rng) => {
  const mu = randInt(rng, 10, 60);
  const sigma = randInt(rng, 2, 10);
  const n = pick(rng, [30, 40, 50, 64, 80]);
  const q = pick(rng, ["mean", "sd"] as const);
  return q === "mean"
    ? numeric("g.clt-sums", `Each of n = ${n} items has mean ${mu} and SD ${sigma}. What is the mean of the sum ΣX?`, n * mu, `μ_ΣX = n·μ = ${n}·${mu} = ${n * mu}.`, { tolerance: 0.011 })
    : numeric("g.clt-sums", `Each of n = ${n} items has mean ${mu} and SD ${sigma}. What is the standard deviation of the sum ΣX? (2 decimals.)`, S.round(Math.sqrt(n) * sigma, 2), `σ_ΣX = √n · σ = √${n} · ${sigma} = ${f(Math.sqrt(n) * sigma)}.`, { tolerance: 0.011 });
});

/* ---------- Chapter 8: confidence intervals ---------- */

export const ciMeanKnownSigma = gen("g.ci-z", (rng) => {
  const xbar = randInt(rng, 40, 120);
  const sigma = randInt(rng, 4, 20);
  const n = pick(rng, [25, 36, 49, 64, 100]);
  const cl = pick(rng, [0.9, 0.95, 0.99]);
  const z = S.normalInv(1 - (1 - cl) / 2);
  const ebm = z * sigma / Math.sqrt(n);
  const q = pick(rng, ["ebm", "lower", "upper"] as const);
  const ans = q === "ebm" ? ebm : q === "lower" ? xbar - ebm : xbar + ebm;
  const lab = q === "ebm" ? "error bound (margin of error) EBM" : q === "lower" ? "lower bound of the confidence interval" : "upper bound of the confidence interval";
  return numeric("g.ci-z", `x̄ = ${xbar}, σ = ${sigma} (known), n = ${n}, confidence level ${cl * 100}%. Find the ${lab}. (2 decimals.)`, S.round(ans, 2), `z_(α/2) = ${f(z, 3)}. EBM = z·σ/√n = ${f(z, 3)}·${sigma}/√${n} = ${f(ebm)}. CI = x̄ ± EBM = (${f(xbar - ebm)}, ${f(xbar + ebm)}).`, { tolerance: 0.03 });
});

export const ciMeanT = gen("g.ci-t", (rng) => {
  const xbar = randInt(rng, 20, 80);
  const s = randInt(rng, 3, 15);
  const n = randInt(rng, 8, 25);
  const cl = pick(rng, [0.9, 0.95, 0.99]);
  const t = S.tInv(1 - (1 - cl) / 2, n - 1);
  const ebm = t * s / Math.sqrt(n);
  const q = pick(rng, ["t", "ebm", "upper"] as const);
  if (q === "t") return numeric("g.ci-t", `A ${cl * 100}% confidence interval for μ uses a sample of n = ${n} with unknown σ. Which t critical value is used? (3 decimals.)`, S.round(t, 3), `df = n − 1 = ${n - 1}; t_(α/2) with α/2 = ${f((1 - cl) / 2, 3)} in each tail is invT(${f(1 - (1 - cl) / 2, 3)}, ${n - 1}) = ${f(t, 3)}.`, { tolerance: 0.01 });
  const ans = q === "ebm" ? ebm : xbar + ebm;
  return numeric("g.ci-t", `x̄ = ${xbar}, s = ${s}, n = ${n}, ${cl * 100}% confidence, σ unknown. Find the ${q === "ebm" ? "error bound EBM" : "upper bound of the interval"}. (2 decimals.)`, S.round(ans, 2), `df = ${n - 1}, t_(α/2) = ${f(t, 3)}. EBM = t·s/√n = ${f(t, 3)}·${s}/√${n} = ${f(ebm)}. Upper bound = ${xbar} + ${f(ebm)} = ${f(xbar + ebm)}.`, { tolerance: 0.05 });
});

export const ciProportion = gen("g.ci-p", (rng) => {
  const n = pick(rng, [100, 200, 250, 400, 500, 1000]);
  const x = randInt(rng, Math.floor(n * 0.2), Math.floor(n * 0.8));
  const cl = pick(rng, [0.9, 0.95, 0.99]);
  const p = x / n;
  const z = S.normalInv(1 - (1 - cl) / 2);
  const ebp = z * Math.sqrt(p * (1 - p) / n);
  const q = pick(rng, ["ebp", "lower"] as const);
  const ans = q === "ebp" ? ebp : p - ebp;
  return numeric("g.ci-p", `In a sample of ${n} people, ${x} say yes. Find the ${q === "ebp" ? "error bound EBP" : "lower bound"} of a ${cl * 100}% confidence interval for the population proportion. (3 decimals.)`, S.round(ans, 3), `p′ = ${x}/${n} = ${f(p, 3)}, q′ = ${f(1 - p, 3)}. EBP = z·√(p′q′/n) = ${f(z, 3)}·√(${f(p, 3)}·${f(1 - p, 3)}/${n}) = ${f(ebp, 3)}. CI = (${f(p - ebp, 3)}, ${f(p + ebp, 3)}).`, { tolerance: 0.003 });
});

export const sampleSizeForMean = gen("g.sample-size", (rng) => {
  const sigma = randInt(rng, 5, 30);
  const E = randInt(rng, 1, 5);
  const cl = pick(rng, [0.9, 0.95, 0.99]);
  const z = S.normalInv(1 - (1 - cl) / 2);
  const n = Math.ceil((z * sigma / E) ** 2);
  return numeric("g.sample-size", `How large a sample is needed to estimate μ within ${E} units with ${cl * 100}% confidence, if σ = ${sigma}? (Round up to a whole number.)`, n, `n = (z·σ/E)² = (${f(z, 3)}·${sigma}/${E})² = ${f((z * sigma / E) ** 2, 2)} → round UP to ${n}.`, { tolerance: 0 });
});

/* ---------- Chapter 9: hypothesis testing ---------- */

export const hypothesisSetup = gen("g.hypotheses", (rng) => {
  const sc = pick(rng, [
    { s: "A cereal box claims to contain 500 g. A consumer group suspects the mean is less.", h: "H₀: μ = 500, Hₐ: μ < 500", w: ["H₀: μ < 500, Hₐ: μ = 500", "H₀: μ = 500, Hₐ: μ ≠ 500", "H₀: μ = 500, Hₐ: μ > 500"] },
    { s: "A politician claims at least 60% of voters support her. An opponent believes it is less than 60%.", h: "H₀: p = 0.60, Hₐ: p < 0.60", w: ["H₀: p < 0.60, Hₐ: p = 0.60", "H₀: p = 0.60, Hₐ: p > 0.60", "H₀: p ≠ 0.60, Hₐ: p = 0.60"] },
    { s: "A tutoring program claims it raises the mean SAT math score above 520.", h: "H₀: μ = 520, Hₐ: μ > 520", w: ["H₀: μ > 520, Hₐ: μ = 520", "H₀: μ = 520, Hₐ: μ < 520", "H₀: μ = 520, Hₐ: μ ≠ 520"] },
    { s: "A factory believes its defect rate is 3%. A manager wants to test whether it has changed.", h: "H₀: p = 0.03, Hₐ: p ≠ 0.03", w: ["H₀: p ≠ 0.03, Hₐ: p = 0.03", "H₀: p = 0.03, Hₐ: p > 0.03", "H₀: p = 0.03, Hₐ: p < 0.03"] },
    { s: "The mean commute time in a city was 27 minutes. A planner tests whether it is now different.", h: "H₀: μ = 27, Hₐ: μ ≠ 27", w: ["H₀: μ ≠ 27, Hₐ: μ = 27", "H₀: μ = 27, Hₐ: μ > 27", "H₀: x̄ = 27, Hₐ: x̄ ≠ 27"] },
  ]);
  return mc("g.hypotheses", "Which pair of hypotheses is correct?", sc.h, sc.w, `The null hypothesis always contains equality and states the status quo or claim. The alternative reflects what the researcher suspects (<, >, or ≠). Hypotheses are always about population parameters (μ, p), never sample statistics.`, rng, sc.s);
});

export const pValueDecision = gen("g.pvalue-decision", (rng) => {
  const alpha = pick(rng, [0.01, 0.05, 0.10]);
  const reject = rng() < 0.5;
  const p = reject ? S.round(alpha * (0.1 + 0.8 * rng()), 4) : S.round(alpha + (0.5 - alpha) * rng(), 4);
  return mc("g.pvalue-decision", `A hypothesis test gives p-value = ${p}. At significance level α = ${alpha}, what is the decision?`, reject ? "Reject H₀ because p-value < α" : "Do not reject H₀ because p-value > α", reject ? ["Do not reject H₀ because p-value > α", "Accept H₀", "Reject Hₐ because p-value < α"] : ["Reject H₀ because p-value < α", "Accept H₀ as proven true", "Reject Hₐ because p-value > α"], `Compare p-value to α: ${p} ${reject ? "<" : ">"} ${alpha}. ${reject ? "A small p-value means the data would be rare if H₀ were true, so we reject H₀." : "The p-value is not small enough; we fail to reject H₀ (we never 'accept' or 'prove' it)."}`, rng);
});

export const zTestStatistic = gen("g.z-test-stat", (rng) => {
  const mu0 = randInt(rng, 40, 120);
  const sigma = randInt(rng, 5, 20);
  const n = pick(rng, [25, 36, 49, 64, 100]);
  const xbar = mu0 + pick(rng, [-3, -2, -1, 1, 2, 3]) * sigma / Math.sqrt(n) + (rng() - 0.5);
  const z = (xbar - mu0) / (sigma / Math.sqrt(n));
  return numeric("g.z-test-stat", `Test H₀: μ = ${mu0} with σ = ${sigma} known, n = ${n}, and x̄ = ${f(xbar, 2)}. Compute the test statistic z. (2 decimals.)`, S.round(z, 2), `z = (x̄ − μ₀)/(σ/√n) = (${f(xbar, 2)} − ${mu0})/(${sigma}/√${n}) = ${f(z)}.`, { tolerance: 0.02 });
});

export const tTestStatistic = gen("g.t-test-stat", (rng) => {
  const mu0 = randInt(rng, 20, 80);
  const s = randInt(rng, 3, 15);
  const n = randInt(rng, 8, 30);
  const xbar = mu0 + pick(rng, [-2.5, -1.5, -1, 1, 1.5, 2.5]) * s / Math.sqrt(n);
  const t = (xbar - mu0) / (s / Math.sqrt(n));
  const q = pick(rng, ["t", "p"] as const);
  if (q === "t") return numeric("g.t-test-stat", `Test H₀: μ = ${mu0} vs Hₐ: μ ≠ ${mu0}. Sample: n = ${n}, x̄ = ${f(xbar, 2)}, s = ${s}. Compute the test statistic t. (2 decimals.)`, S.round(t, 2), `t = (x̄ − μ₀)/(s/√n) = (${f(xbar, 2)} − ${mu0})/(${s}/√${n}) = ${f(t)}, with df = ${n - 1}.`, { tolerance: 0.02 });
  const p = 2 * (1 - S.tCDF(Math.abs(t), n - 1));
  return numeric("g.t-test-stat", `Test H₀: μ = ${mu0} vs Hₐ: μ ≠ ${mu0}. Sample: n = ${n}, x̄ = ${f(xbar, 2)}, s = ${s}. Find the two-tailed p-value. (4 decimals.)`, S.round(p, 4), `t = ${f(t)}, df = ${n - 1}. Two-tailed p-value = 2·P(T > |${f(t)}|) = ${f(p, 4)} (calculator: T-Test).`, { tolerance: 0.004 });
});

export const proportionTest = gen("g.prop-test", (rng) => {
  const p0 = pick(rng, [0.3, 0.4, 0.5, 0.6, 0.7]);
  const n = pick(rng, [100, 150, 200, 300, 400]);
  const x = Math.round(n * (p0 + pick(rng, [-0.08, -0.05, 0.05, 0.08])));
  const pp = x / n;
  const z = (pp - p0) / Math.sqrt(p0 * (1 - p0) / n);
  return numeric("g.prop-test", `Test H₀: p = ${p0}. In a sample of n = ${n}, x = ${x} successes. Compute the test statistic z. (2 decimals.)`, S.round(z, 2), `p′ = ${x}/${n} = ${f(pp, 3)}. z = (p′ − p₀)/√(p₀q₀/n) = (${f(pp, 3)} − ${p0})/√(${p0}·${f(1 - p0)}/${n}) = ${f(z)}.`, { tolerance: 0.03 });
});

export const errorTypes = gen("g.error-types", (rng) => {
  const sc = pick(rng, [
    { h0: "the patient does not have the disease", t1: "Telling a healthy patient they have the disease", t2: "Telling a sick patient they are healthy" },
    { h0: "the defendant is innocent", t1: "Convicting an innocent person", t2: "Acquitting a guilty person" },
    { h0: "the bridge is safe", t1: "Closing a bridge that is actually safe", t2: "Keeping open a bridge that is actually unsafe" },
    { h0: "the new drug has no effect", t1: "Approving a drug that actually does nothing", t2: "Rejecting a drug that actually works" },
  ]);
  const askType1 = rng() < 0.5;
  return mc("g.error-types", `H₀: ${sc.h0}. Which of these is a ${askType1 ? "Type I" : "Type II"} error?`, askType1 ? sc.t1 : sc.t2, [askType1 ? sc.t2 : sc.t1, "Failing to collect a sample", "Choosing α = 0.05"], `Type I error = rejecting a TRUE null hypothesis (probability α). Type II error = failing to reject a FALSE null hypothesis (probability β). Here H₀ is "${sc.h0}", so ${askType1 ? `"${sc.t1}" rejects a true H₀.` : `"${sc.t2}" fails to reject a false H₀.`}`, rng);
});

/* ---------- Chapter 10: two samples ---------- */

export const twoMeansStat = gen("g.two-means", (rng) => {
  const x1 = randInt(rng, 40, 80), x2 = x1 + pick(rng, [-6, -4, -3, 3, 4, 6]);
  const s1 = randInt(rng, 4, 12), s2 = randInt(rng, 4, 12);
  const n1 = randInt(rng, 15, 40), n2 = randInt(rng, 15, 40);
  const se = Math.sqrt(s1 ** 2 / n1 + s2 ** 2 / n2);
  const t = (x1 - x2) / se;
  const q = pick(rng, ["se", "t"] as const);
  const ctx = `Group 1: x̄₁ = ${x1}, s₁ = ${s1}, n₁ = ${n1}. Group 2: x̄₂ = ${x2}, s₂ = ${s2}, n₂ = ${n2}. Independent samples, σ unknown.`;
  return q === "se"
    ? numeric("g.two-means", "Find the standard error √(s₁²/n₁ + s₂²/n₂). (3 decimals.)", S.round(se, 3), `√(${s1}²/${n1} + ${s2}²/${n2}) = √(${f(s1 ** 2 / n1, 3)} + ${f(s2 ** 2 / n2, 3)}) = ${f(se, 3)}.`, { context: ctx, tolerance: 0.003 })
    : numeric("g.two-means", "Compute the test statistic t for H₀: μ₁ − μ₂ = 0. (2 decimals.)", S.round(t, 2), `t = (x̄₁ − x̄₂ − 0)/√(s₁²/n₁ + s₂²/n₂) = (${x1} − ${x2})/${f(se, 3)} = ${f(t)}.`, { context: ctx, tolerance: 0.03 });
});

export const twoProportionsStat = gen("g.two-props", (rng) => {
  const n1 = pick(rng, [100, 150, 200, 250]), n2 = pick(rng, [100, 150, 200, 250]);
  const x1 = randInt(rng, Math.floor(n1 * 0.3), Math.floor(n1 * 0.7));
  const x2 = randInt(rng, Math.floor(n2 * 0.3), Math.floor(n2 * 0.7));
  const pc = (x1 + x2) / (n1 + n2);
  const z = (x1 / n1 - x2 / n2) / Math.sqrt(pc * (1 - pc) * (1 / n1 + 1 / n2));
  const q = pick(rng, ["pc", "z"] as const);
  const ctx = `Sample 1: x₁ = ${x1} of n₁ = ${n1}. Sample 2: x₂ = ${x2} of n₂ = ${n2}.`;
  return q === "pc"
    ? numeric("g.two-props", "Find the pooled proportion p_c = (x₁ + x₂)/(n₁ + n₂). (3 decimals.)", S.round(pc, 3), `(${x1} + ${x2})/(${n1} + ${n2}) = ${f(pc, 3)}.`, { context: ctx, tolerance: 0.002 })
    : numeric("g.two-props", "Compute z for testing H₀: p₁ = p₂. (2 decimals.)", S.round(z, 2), `p′₁ = ${f(x1 / n1, 3)}, p′₂ = ${f(x2 / n2, 3)}, p_c = ${f(pc, 3)}. z = (p′₁ − p′₂)/√(p_c(1−p_c)(1/n₁ + 1/n₂)) = ${f(z)}.`, { context: ctx, tolerance: 0.03 });
});

export const pairedDifferences = gen("g.paired", (rng) => {
  const n = randInt(rng, 5, 7);
  const before = dataset(rng, n, 60, 90);
  const after = before.map((b) => b + randInt(rng, -3, 8));
  const d = after.map((a, i) => a - before[i]);
  const dbar = S.mean(d);
  const sd = S.sampleSD(d);
  const q = pick(rng, ["dbar", "t"] as const);
  const ctx = `Before: ${list(before)}\nAfter:  ${list(after)}\n(differences = after − before)`;
  if (q === "dbar") return numeric("g.paired", "Find the mean of the differences, d̄. (2 decimals.)", S.round(dbar, 2), `Differences: ${list(d)}. d̄ = ${d.reduce((a, b) => a + b, 0)}/${n} = ${f(dbar)}.`, { context: ctx, tolerance: 0.011 });
  const t = dbar / (sd / Math.sqrt(n));
  return numeric("g.paired", "Compute t = d̄/(s_d/√n) for testing H₀: μ_d = 0. (2 decimals.)", S.round(t, 2), `Differences: ${list(d)}. d̄ = ${f(dbar)}, s_d = ${f(sd, 3)}. t = ${f(dbar)}/(${f(sd, 3)}/√${n}) = ${f(t)}, df = ${n - 1}.`, { context: ctx, tolerance: 0.05 });
});

/* ---------- Chapter 11: chi-square ---------- */

export const chiSquareGOF = gen("g.chi-gof", (rng) => {
  const k = randInt(rng, 3, 5);
  const n = pick(rng, [60, 100, 120, 200]);
  const expected = n / k;
  const observed = Array.from({ length: k }, () => Math.round(expected + randInt(rng, -8, 8)));
  const diff = n - observed.reduce((a, b) => a + b, 0);
  observed[0] += diff;
  const chi = observed.reduce((acc, o) => acc + (o - expected) ** 2 / expected, 0);
  const q = pick(rng, ["stat", "df"] as const);
  const ctx = `A die-like spinner with ${k} equally likely outcomes is spun ${n} times. Observed counts: ${list(observed)}.`;
  return q === "df"
    ? numeric("g.chi-gof", "How many degrees of freedom does the goodness-of-fit test have?", k - 1, `df = (number of categories) − 1 = ${k} − 1 = ${k - 1}.`, { context: ctx, tolerance: 0 })
    : numeric("g.chi-gof", `Each expected count is ${f(expected)}. Compute the χ² test statistic Σ (O − E)²/E. (2 decimals.)`, S.round(chi, 2), `χ² = ${observed.map((o) => `(${o}−${f(expected)})²/${f(expected)}`).join(" + ")} = ${f(chi)}.`, { context: ctx, tolerance: 0.03 });
});

export const chiSquareIndependence = gen("g.chi-indep", (rng) => {
  const a = randInt(rng, 20, 60), b = randInt(rng, 20, 60), c = randInt(rng, 20, 60), d = randInt(rng, 20, 60);
  const n = a + b + c + d;
  const r1 = a + b, r2 = c + d, c1 = a + c, c2 = b + d;
  const E = [r1 * c1 / n, r1 * c2 / n, r2 * c1 / n, r2 * c2 / n];
  const O = [a, b, c, d];
  const chi = O.reduce((acc, o, i) => acc + (o - E[i]) ** 2 / E[i], 0);
  const q = pick(rng, ["expected", "stat", "df"] as const);
  const ctx = `Observed table:\n           Yes  | No\n  Group A  ${a}  | ${b}\n  Group B  ${c}  | ${d}`;
  if (q === "df") return numeric("g.chi-indep", "For a test of independence on this 2×2 table, what is df?", 1, "df = (rows − 1)(columns − 1) = (2 − 1)(2 − 1) = 1.", { context: ctx, tolerance: 0 });
  if (q === "expected") return numeric("g.chi-indep", "Find the expected count for the Group A / Yes cell. (2 decimals.)", S.round(E[0], 2), `E = (row total)(column total)/n = (${r1})(${c1})/${n} = ${f(E[0])}.`, { context: ctx, tolerance: 0.02 });
  return numeric("g.chi-indep", "Compute the χ² test statistic. (2 decimals.)", S.round(chi, 2), `Expected counts: ${E.map((e) => f(e)).join(", ")}. χ² = Σ(O−E)²/E = ${f(chi)}, df = 1.`, { context: ctx, tolerance: 0.05 });
});

export const singleVarianceTest = gen("g.var-test", (rng) => {
  const sigma0 = randInt(rng, 3, 10);
  const n = randInt(rng, 10, 30);
  const s = sigma0 + pick(rng, [-2, -1, 1, 2, 3]);
  const chi = (n - 1) * s ** 2 / sigma0 ** 2;
  return numeric("g.var-test", `Test H₀: σ² = ${sigma0 ** 2} (σ = ${sigma0}) using n = ${n} and sample SD s = ${s}. Compute χ² = (n − 1)s²/σ². (2 decimals.)`, S.round(chi, 2), `χ² = (${n} − 1)(${s}²)/${sigma0}² = ${n - 1}·${s ** 2}/${sigma0 ** 2} = ${f(chi)}, df = ${n - 1}.`, { tolerance: 0.03 });
});

/* ---------- Chapter 12: regression ---------- */

export const linearEquation = gen("g.linear-eq", (rng) => {
  const a = randInt(rng, 5, 50), b = randInt(rng, 2, 15);
  const x = randInt(rng, 2, 20);
  const q = pick(rng, ["predict", "slope", "intercept"] as const);
  const ctx = `A tutoring service charges according to ŷ = ${a} + ${b}x, where x = hours and ŷ = total cost in dollars.`;
  if (q === "predict") return numeric("g.linear-eq", `What is the predicted cost for x = ${x} hours?`, a + b * x, `ŷ = ${a} + ${b}(${x}) = ${a + b * x}.`, { context: ctx, tolerance: 0.011 });
  if (q === "slope") return mc("g.linear-eq", "What does the slope tell us?", `Each additional hour adds $${b} to the cost`, [`The base fee is $${b}`, `The cost for one hour is $${b}`, `Cost decreases by $${b} per hour`], `The slope b = ${b} is the change in y per one-unit change in x: each extra hour costs $${b} more. The y-intercept ${a} is the cost when x = 0 (a fixed fee).`, rng, ctx);
  return mc("g.linear-eq", "What does the y-intercept tell us?", `There is a fixed charge of $${a} even with zero hours`, [`Each hour costs $${a}`, `The maximum cost is $${a}`, `The service starts at hour ${a}`], `The y-intercept a = ${a} is the value of ŷ when x = 0: a fixed fee of $${a}.`, rng, ctx);
});

export const regressionFromData = gen("g.regression", (rng) => {
  const n = 5;
  const xs = Array.from({ length: n }, (_, i) => i + 1 + randInt(rng, 0, 1));
  const trueB = pick(rng, [-3, -2, 2, 3, 4]);
  const trueA = randInt(rng, 5, 30);
  const ys = xs.map((x) => trueA + trueB * x + randInt(rng, -2, 2));
  const { a, b, r } = S.regression(xs, ys);
  const q = pick(rng, ["slope", "intercept", "r", "predict"] as const);
  const ctx = `x: ${list(xs)}\ny: ${list(ys)}`;
  if (q === "slope") return numeric("g.regression", "Find the slope b of the least-squares line ŷ = a + bx. (3 decimals.)", S.round(b, 3), `b = Σ(x−x̄)(y−ȳ)/Σ(x−x̄)² = ${f(b, 3)} (calculator: LinRegTTest). Line: ŷ = ${f(a, 2)} + ${f(b, 3)}x.`, { context: ctx, tolerance: 0.01 });
  if (q === "intercept") return numeric("g.regression", "Find the y-intercept a of the least-squares line ŷ = a + bx. (2 decimals.)", S.round(a, 2), `a = ȳ − b·x̄ = ${f(S.mean(ys), 2)} − (${f(b, 3)})(${f(S.mean(xs), 2)}) = ${f(a, 2)}.`, { context: ctx, tolerance: 0.05 });
  if (q === "r") return numeric("g.regression", "Find the correlation coefficient r. (3 decimals.)", S.round(r, 3), `r = ${f(r, 3)}. It has the same sign as the slope (${trueB > 0 ? "positive" : "negative"}) and is close to ±1 because the points lie near a line.`, { context: ctx, tolerance: 0.01 });
  const x0 = Math.max(...xs) + 1;
  return numeric("g.regression", `Use the least-squares line to predict y when x = ${x0}. (2 decimals.)`, S.round(a + b * x0, 2), `ŷ = ${f(a, 2)} + ${f(b, 3)}(${x0}) = ${f(a + b * x0, 2)}.`, { context: ctx, tolerance: 0.1 });
});

export const correlationStrength = gen("g.corr-strength", (rng) => {
  const r = pick(rng, [-0.95, -0.7, -0.3, -0.05, 0.1, 0.4, 0.75, 0.98]);
  const dir = r > 0 ? "positive" : "negative";
  const strength = Math.abs(r) >= 0.7 ? "strong" : Math.abs(r) >= 0.3 ? "moderate" : "weak or no";
  const ans = `${strength} ${dir} linear relationship`;
  const all = ["strong positive linear relationship", "strong negative linear relationship", "moderate positive linear relationship", "moderate negative linear relationship", "weak or no positive linear relationship", "weak or no negative linear relationship"];
  return mc("g.corr-strength", `The correlation coefficient is r = ${r}. How would you describe the relationship?`, ans, shuffle(rng, all.filter((s) => s !== ans)).slice(0, 3), `The sign of r gives direction (${dir}); |r| = ${Math.abs(r)} gives strength (near 1 = strong, near 0 = weak). r² = ${f(r * r, 3)} is the fraction of variation in y explained by the line.`, rng);
});

export const rCritical = gen("g.r-critical", (rng) => {
  const n = randInt(rng, 6, 30);
  const r = pick(rng, [0.3, 0.4, 0.5, 0.6, 0.7, 0.8]) * (rng() < 0.5 ? -1 : 1);
  const df = n - 2;
  const t = r * Math.sqrt(df / (1 - r * r));
  const p = 2 * (1 - S.tCDF(Math.abs(t), df));
  const sig = p < 0.05;
  return mc("g.r-critical", `With n = ${n} data points, r = ${r}. At α = 0.05, is the correlation significant (p-value = ${f(p, 4)})?`, sig ? "Yes: reject H₀: ρ = 0, so the line can be used for prediction" : "No: do not reject H₀: ρ = 0, so the line should not be used for prediction", sig ? ["No: do not reject H₀: ρ = 0, so the line should not be used for prediction", "Yes, because r is positive", "No, because n is small"] : ["Yes: reject H₀: ρ = 0, so the line can be used for prediction", "Yes, because |r| > 0", "No, because r is negative"], `Test statistic t = r√((n−2)/(1−r²)) = ${f(t, 3)} with df = n − 2 = ${df}; p-value = ${f(p, 4)} ${sig ? "<" : ">"} 0.05. ${sig ? "Significant: there is evidence of a linear relationship in the population." : "Not significant: not enough evidence of a linear relationship."}`, rng);
});

/* ---------- Chapter 13: ANOVA / F ---------- */

export const anovaDF = gen("g.anova-df", (rng) => {
  const k = randInt(rng, 3, 6);
  const sizes = Array.from({ length: k }, () => randInt(rng, 4, 10));
  const N = sizes.reduce((a, b) => a + b, 0);
  const q = pick(rng, ["between", "within", "total"] as const);
  const ans = q === "between" ? k - 1 : q === "within" ? N - k : N - 1;
  const ctx = `One-way ANOVA comparing ${k} groups with sizes ${list(sizes)} (N = ${N}).`;
  return numeric("g.anova-df", `What is df(${q})?`, ans, `df(between) = k − 1 = ${k - 1}; df(within) = N − k = ${N - k}; df(total) = N − 1 = ${N - 1}.`, { context: ctx, tolerance: 0 });
});

export const anovaFRatio = gen("g.anova-f", (rng) => {
  const k = randInt(rng, 3, 5);
  const N = k * randInt(rng, 5, 10);
  const ssb = randInt(rng, 50, 400);
  const ssw = randInt(rng, 200, 1500);
  const msb = ssb / (k - 1), msw = ssw / (N - k);
  const F = msb / msw;
  const q = pick(rng, ["msb", "msw", "F"] as const);
  const ctx = `ANOVA: k = ${k} groups, N = ${N} total observations, SS(between) = ${ssb}, SS(within) = ${ssw}.`;
  if (q === "msb") return numeric("g.anova-f", "Find MS(between) = SS(between)/df(between). (2 decimals.)", S.round(msb, 2), `${ssb}/(${k} − 1) = ${f(msb)}.`, { context: ctx, tolerance: 0.02 });
  if (q === "msw") return numeric("g.anova-f", "Find MS(within) = SS(within)/df(within). (2 decimals.)", S.round(msw, 2), `${ssw}/(${N} − ${k}) = ${f(msw)}.`, { context: ctx, tolerance: 0.02 });
  return numeric("g.anova-f", "Compute the F statistic = MS(between)/MS(within). (2 decimals.)", S.round(F, 2), `MS(between) = ${f(msb)}, MS(within) = ${f(msw)}. F = ${f(msb)}/${f(msw)} = ${f(F)} with df = (${k - 1}, ${N - k}). p-value = ${f(1 - S.fCDF(F, k - 1, N - k), 4)}.`, { context: ctx, tolerance: 0.05 });
});

export const twoVariancesF = gen("g.two-var-f", (rng) => {
  const s1 = randInt(rng, 3, 12), s2 = randInt(rng, 3, 12);
  const n1 = randInt(rng, 8, 25), n2 = randInt(rng, 8, 25);
  const F = s1 ** 2 / s2 ** 2;
  return numeric("g.two-var-f", `Test H₀: σ₁² = σ₂². Sample 1: s₁ = ${s1}, n₁ = ${n1}. Sample 2: s₂ = ${s2}, n₂ = ${n2}. Compute F = s₁²/s₂². (3 decimals.)`, S.round(F, 3), `F = ${s1}²/${s2}² = ${s1 ** 2}/${s2 ** 2} = ${f(F, 3)}, with df = (${n1 - 1}, ${n2 - 1}).`, { tolerance: 0.005 });
});


/* ---------- extra generators for lessons without numeric drills ---------- */

export const missingProbability = gen("g.missing-prob", (rng) => {
  const xs = [0, 1, 2, 3];
  const w = [randInt(rng, 1, 6), randInt(rng, 1, 6), randInt(rng, 1, 6), randInt(rng, 1, 6)];
  const tot = w.reduce((a, b) => a + b, 0);
  const ps = w.map((v) => S.round(v / tot, 2));
  ps[3] = S.round(1 - ps[0] - ps[1] - ps[2], 2);
  const hide = randInt(rng, 0, 3);
  const q = pick(rng, ["missing", "atleast", "atmost"] as const);
  const table = xs.map((x, i) => `x=${x}: P=${i === hide && q === "missing" ? "?" : ps[i]}`).join(" | ");
  if (q === "missing") return numeric("g.missing-prob", `Find the missing probability P(X = ${xs[hide]}). (2 decimals.)`, ps[hide], `Probabilities must add to 1: 1 − (${ps.filter((_, i) => i !== hide).join(" + ")}) = ${f(ps[hide])}.`, { context: `Probability distribution: ${table}`, tolerance: 0.006 });
  const k = randInt(rng, 1, 2);
  const v = q === "atleast" ? ps.slice(k).reduce((a, b) => a + b, 0) : ps.slice(0, k + 1).reduce((a, b) => a + b, 0);
  return numeric("g.missing-prob", `Find P(X ${q === "atleast" ? "≥" : "≤"} ${k}). (2 decimals.)`, S.round(v, 2), `Add the probabilities for x ${q === "atleast" ? "≥" : "≤"} ${k}: ${(q === "atleast" ? ps.slice(k) : ps.slice(0, k + 1)).join(" + ")} = ${f(v)}.`, { context: `Probability distribution: ${table}`, tolerance: 0.006 });
});

export const twoMeansKnownSigma = gen("g.two-means-z", (rng) => {
  const x1 = randInt(rng, 40, 90), x2 = x1 + pick(rng, [-5, -4, -3, -2, 2, 3, 4, 5]);
  const s1 = randInt(rng, 4, 12), s2 = randInt(rng, 4, 12);
  const n1 = pick(rng, [30, 40, 50, 60]), n2 = pick(rng, [30, 40, 50, 60]);
  const se = Math.sqrt(s1 ** 2 / n1 + s2 ** 2 / n2);
  const z = (x1 - x2) / se;
  const ctx = `Group 1: x̄₁ = ${x1}, σ₁ = ${s1} (known), n₁ = ${n1}. Group 2: x̄₂ = ${x2}, σ₂ = ${s2} (known), n₂ = ${n2}.`;
  const q = pick(rng, ["z", "p"] as const);
  if (q === "z") return numeric("g.two-means-z", "Compute z for H₀: μ₁ − μ₂ = 0. (2 decimals.)", S.round(z, 2), `z = (x̄₁ − x̄₂)/√(σ₁²/n₁ + σ₂²/n₂) = (${x1} − ${x2})/√(${s1}²/${n1} + ${s2}²/${n2}) = (${x1 - x2})/${f(se, 3)} = ${f(z)}.`, { context: ctx, tolerance: 0.03 });
  const pv = 2 * (1 - S.normalCDF(Math.abs(z)));
  return numeric("g.two-means-z", "Find the two-tailed p-value for H₀: μ₁ = μ₂ vs Hₐ: μ₁ ≠ μ₂. (4 decimals.)", S.round(pv, 4), `z = ${f(z)}. Two-tailed p-value = 2·P(Z > |${f(z)}|) = ${f(pv, 4)}.`, { context: ctx, tolerance: 0.003 });
});

export const chiSquareFacts = gen("g.chi-facts", (rng) => {
  const df = pick(rng, [2, 4, 6, 8, 10, 12, 18, 24, 32, 50]);
  const q = pick(rng, ["mean", "sd", "crit"] as const);
  if (q === "mean") return numeric("g.chi-facts", `What is the mean of a chi-square distribution with ${df} degrees of freedom?`, df, `For χ², the mean equals the degrees of freedom: ${df}.`, { tolerance: 0 });
  if (q === "sd") return numeric("g.chi-facts", `What is the standard deviation of a chi-square distribution with ${df} degrees of freedom? (2 decimals.)`, S.round(Math.sqrt(2 * df), 2), `σ = √(2·df) = √${2 * df} = ${f(Math.sqrt(2 * df))}.`, { tolerance: 0.011 });
  const alpha = pick(rng, [0.1, 0.05, 0.01]);
  const crit = S.chiSquareInv(1 - alpha, df);
  return numeric("g.chi-facts", `For a right-tailed χ² test with df = ${df} and α = ${alpha}, what is the critical value? (2 decimals.)`, S.round(crit, 2), `The critical value leaves area ${alpha} in the right tail: χ²(${1 - alpha}, ${df}) = ${f(crit)}. Reject H₀ when the statistic exceeds it.`, { tolerance: 0.05 });
});

export const residualOutlier = gen("g.residual", (rng) => {
  const a = randInt(rng, 2, 20), b = pick(rng, [1.5, 2, 2.5, 3, -2, -1.5]);
  const x = randInt(rng, 2, 15);
  const yhat = a + b * x;
  const s = pick(rng, [2, 2.5, 3, 4]);
  const resid = pick(rng, [-3, -2.5, -1, 0.5, 1, 1.5, 2.5, 3]) * s / 1.2;
  const y = S.round(yhat + resid, 1);
  const r = y - yhat;
  const q = pick(rng, ["resid", "outlier"] as const);
  const ctx = `Regression line: ŷ = ${a} + ${b}x. A data point has x = ${x}, y = ${y}.`;
  if (q === "resid") return numeric("g.residual", "Find the residual y − ŷ for this point. (1 decimal.)", S.round(r, 1), `ŷ = ${a} + ${b}(${x}) = ${f(yhat, 1)}. Residual = ${y} − ${f(yhat, 1)} = ${f(r, 1)}.`, { context: ctx, tolerance: 0.06 });
  const isOut = Math.abs(r) >= 2 * s;
  return mc("g.residual", `The standard deviation of the residuals is s = ${s}. Is this point an outlier by the 2s rule?`, isOut ? `Yes: |residual| = ${f(Math.abs(r), 1)} is at least 2s = ${2 * s}` : `No: |residual| = ${f(Math.abs(r), 1)} is less than 2s = ${2 * s}`, [isOut ? `No: |residual| = ${f(Math.abs(r), 1)} is less than 2s = ${2 * s}` : `Yes: |residual| = ${f(Math.abs(r), 1)} is at least 2s = ${2 * s}`, "Yes, because the residual is negative", "No, because x is inside the data range"], `ŷ = ${f(yhat, 1)}, residual = ${f(r, 1)}. The book's rule flags a point when |residual| ≥ 2s = ${2 * s} (equivalently, the point lies above ŷ + 2s or below ŷ − 2s); here that is ${isOut ? "true" : "false"}.`, rng, ctx);
});

/** Percentile of a given value: (x + 0.5y)/n × 100, x = values below, y = values equal. */
export const percentileOfValue = gen("g.percentile-of-value", (rng) => {
  const n = randInt(rng, 10, 16);
  const xs = Array.from({ length: n }, () => randInt(rng, 1, 12)).sort((a, b) => a - b);
  const v = xs[randInt(rng, 2, n - 3)];
  const below = xs.filter((x) => x < v).length;
  const equal = xs.filter((x) => x === v).length;
  const pct = ((below + 0.5 * equal) / n) * 100;
  return numeric("g.percentile-of-value", `What is the percentile of the value ${v}? (Round to the nearest whole percent.)`, Math.round(pct), `Count x = ${below} values below ${v} and y = ${equal} value${equal === 1 ? "" : "s"} equal to it. Percentile = (x + 0.5y)/n × 100 = (${below} + ${0.5 * equal})/${n} × 100 = ${f(pct, 1)} → ${Math.round(pct)}th percentile.`, { context: `Ordered data (n = ${n}): ${xs.join(", ")}`, tolerance: 1 });
});

/** Mean of grouped data using interval midpoints: x̄ = Σ(f·m)/Σf. */
export const groupedMean = gen("g.grouped-mean", (rng) => {
  const lo = pick(rng, [0, 10, 20, 50]);
  const w = pick(rng, [5, 10]);
  const k = randInt(rng, 3, 4);
  const freqs = Array.from({ length: k }, () => randInt(rng, 2, 9));
  const rows = freqs.map((fq, i) => ({ a: lo + i * w, b: lo + (i + 1) * w, m: lo + i * w + w / 2, f: fq }));
  const n = freqs.reduce((a, b) => a + b, 0);
  const mean = rows.reduce((acc, r) => acc + r.m * r.f, 0) / n;
  const table = rows.map((r) => `${r.a}–${r.b}: ${r.f}`).join(" | ");
  return numeric("g.grouped-mean", "Estimate the mean from the grouped frequency table using interval midpoints. (2 decimals.)", S.round(mean, 2), `Midpoints m = ${rows.map((r) => r.m).join(", ")}. x̄ ≈ Σ(f·m)/Σf = (${rows.map((r) => `${r.f}·${r.m}`).join(" + ")})/${n} = ${f(rows.reduce((acc, r) => acc + r.m * r.f, 0), 1)}/${n} = ${f(mean)}.`, { context: `Interval: frequency — ${table}`, tolerance: 0.02 });
});

/** Cohen's d effect size for two independent means, with pooled standard deviation. */
export const cohensD = gen("g.cohens-d", (rng) => {
  const s1 = randInt(rng, 4, 12), s2 = randInt(rng, 4, 12);
  const n1 = randInt(rng, 10, 40), n2 = randInt(rng, 10, 40);
  const x1 = randInt(rng, 40, 80);
  const sp = Math.sqrt(((n1 - 1) * s1 ** 2 + (n2 - 1) * s2 ** 2) / (n1 + n2 - 2));
  const x2 = S.round(x1 - pick(rng, [0.15, 0.3, 0.5, 0.6, 0.8, 1.0, 1.2]) * sp, 1);
  const d = (x1 - x2) / sp;
  const ctx = `Group 1: x̄₁ = ${x1}, s₁ = ${s1}, n₁ = ${n1}. Group 2: x̄₂ = ${x2}, s₂ = ${s2}, n₂ = ${n2}.`;
  const q = pick(rng, ["d", "size"] as const);
  const size = Math.abs(d) >= 0.8 ? "large" : Math.abs(d) >= 0.5 ? "medium" : Math.abs(d) >= 0.2 ? "small" : "negligible";
  if (q === "d") return numeric("g.cohens-d", "Compute Cohen's d = (x̄₁ − x̄₂)/s_pooled, where s_pooled = √(((n₁−1)s₁² + (n₂−1)s₂²)/(n₁+n₂−2)). (2 decimals.)", S.round(d, 2), `s_pooled = √(((${n1 - 1})(${s1}²) + (${n2 - 1})(${s2}²))/(${n1 + n2 - 2})) = ${f(sp, 3)}. d = (${x1} − ${x2})/${f(sp, 3)} = ${f(d)}, a ${size} effect.`, { context: ctx, tolerance: 0.03 });
  return mc("g.cohens-d", `Cohen's d for these groups is about ${f(d, 2)}. How large is the effect?`, `${size[0].toUpperCase() + size.slice(1)} (guideline: 0.2 small, 0.5 medium, 0.8 large)`, ["Small (guideline: 0.2 small, 0.5 medium, 0.8 large)", "Medium (guideline: 0.2 small, 0.5 medium, 0.8 large)", "Large (guideline: 0.2 small, 0.5 medium, 0.8 large)", "Negligible (guideline: 0.2 small, 0.5 medium, 0.8 large)"].filter((o) => !o.startsWith(size[0].toUpperCase() + size.slice(1))).slice(0, 3), `Cohen's d expresses the difference in means in units of the pooled standard deviation. Common guidelines: 0.2 small, 0.5 medium, 0.8 large. Here |d| = ${f(Math.abs(d), 2)}, so the effect is ${size}. Effect size describes practical importance and is separate from statistical significance.`, rng, ctx);
});

/** One-way ANOVA with equal group sizes: F = n·(variance of the group means)/(mean of the group variances). */
export const anovaEqualSizes = gen("g.anova-equal", (rng) => {
  const k = randInt(rng, 3, 4);
  const n = randInt(rng, 5, 10);
  const means = Array.from({ length: k }, () => randInt(rng, 40, 70) + pick(rng, [0, 0.5]));
  const vars = Array.from({ length: k }, () => randInt(rng, 10, 40));
  const sx = S.sampleVariance(means);
  const sp = S.mean(vars);
  const F = (n * sx) / sp;
  const ctx = `${k} groups of n = ${n} each. Group means: ${means.join(", ")}. Group variances: ${vars.join(", ")}.`;
  const q = pick(rng, ["F", "dfnum", "dfden"] as const);
  if (q === "dfnum") return numeric("g.anova-equal", "What is the numerator degrees of freedom, df(between)?", k - 1, `df(between) = k − 1 = ${k - 1}.`, { context: ctx, tolerance: 0 });
  if (q === "dfden") return numeric("g.anova-equal", "What is the denominator degrees of freedom, df(within)?", k * n - k, `df(within) = N − k = ${k * n} − ${k} = ${k * n - k}.`, { context: ctx, tolerance: 0 });
  return numeric("g.anova-equal", "Because the groups are the same size, use F = n·s²_x̄ / (mean of the sample variances). Compute F. (2 decimals.)", S.round(F, 2), `Variance of the ${k} group means: s²_x̄ = ${f(sx, 3)}. Mean of the group variances (pooled variance): ${f(sp, 3)}. F = ${n}·${f(sx, 3)}/${f(sp, 3)} = ${f(F)} with df = (${k - 1}, ${k * n - k}); p-value = ${f(1 - S.fCDF(F, k - 1, k * n - k), 4)}.`, { context: ctx, tolerance: 0.05 });
});

/** Mean of the F distribution: df2/(df2 − 2) for df2 > 2. */
export const fDistributionMean = gen("g.f-mean", (rng) => {
  const df1 = randInt(rng, 2, 8), df2 = pick(rng, [10, 12, 15, 20, 24, 30, 40]);
  return numeric("g.f-mean", `What is the mean of the F distribution with df = (${df1}, ${df2})? (3 decimals.)`, S.round(df2 / (df2 - 2), 3), `μ = df(denom)/(df(denom) − 2) = ${df2}/${df2 - 2} = ${f(df2 / (df2 - 2), 3)}. The mean depends only on the denominator degrees of freedom and is a little above 1.`, { tolerance: 0.003 });
});

/** Working backwards from a confidence interval. */
export const ciBackwards = gen("g.ci-backwards", (rng) => {
  const xbar = randInt(rng, 20, 200);
  const ebm = pick(rng, [1.5, 2, 2.5, 3, 4, 5, 6.5, 8]);
  const lo = xbar - ebm, hi = xbar + ebm;
  const q = pick(rng, ["ebm", "mean"] as const);
  const ctx = `A confidence interval for a population mean is (${f(lo, 1)}, ${f(hi, 1)}).`;
  return q === "ebm"
    ? numeric("g.ci-backwards", "What is the error bound EBM? (1 decimal.)", ebm, `EBM is half the width of the interval: (${f(hi, 1)} − ${f(lo, 1)})/2 = ${f(ebm, 1)}. Equivalently, upper bound − sample mean.`, { context: ctx, tolerance: 0.06 })
    : numeric("g.ci-backwards", "What was the sample mean (the point estimate)? (1 decimal.)", xbar, `The point estimate is the midpoint: (${f(lo, 1)} + ${f(hi, 1)})/2 = ${xbar}.`, { context: ctx, tolerance: 0.06 });
});

export const allGenerators: Generator[] = [
  sampleVsPopulation, samplingMethod, relativeFrequency,
  meanOfData, medianOfData, modeOfData, sampleSDOfData, zScoreFromData, valueFromZ, quartilesIQR, outlierFence, percentileInterpretation,
  basicProbability, complementRule, additionRule, conditionalProbability, independenceCheck, contingencyTable,
  expectedValue, binomialProbability, binomialMeanSD, geometricProbability, poissonProbability, hypergeometric,
  uniformProbability, exponentialProbability,
  normalProbability, normalInverse, empiricalRule,
  cltMeans, cltSums,
  ciMeanKnownSigma, ciMeanT, ciProportion, sampleSizeForMean,
  hypothesisSetup, pValueDecision, zTestStatistic, tTestStatistic, proportionTest, errorTypes,
  twoMeansStat, twoProportionsStat, pairedDifferences,
  chiSquareGOF, chiSquareIndependence, singleVarianceTest,
  linearEquation, regressionFromData, correlationStrength, rCritical,
  anovaDF, anovaFRatio, twoVariancesF,
  missingProbability, twoMeansKnownSigma, chiSquareFacts, residualOutlier,
  percentileOfValue, groupedMean, cohensD, anovaEqualSizes, fDistributionMean, ciBackwards,
];

export type { Exercise };
