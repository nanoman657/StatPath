/** Numerical helpers used by generators, grading, and explanations. */

export const mean = (xs: number[]): number => xs.reduce((a, b) => a + b, 0) / xs.length;

export const median = (xs: number[]): number => {
  const s = [...xs].sort((a, b) => a - b);
  const n = s.length;
  return n % 2 ? s[(n - 1) / 2] : (s[n / 2 - 1] + s[n / 2]) / 2;
};

export const mode = (xs: number[]): number[] => {
  const counts = new Map<number, number>();
  xs.forEach((x) => counts.set(x, (counts.get(x) ?? 0) + 1));
  const max = Math.max(...counts.values());
  if (max === 1) return [];
  return [...counts.entries()].filter(([, c]) => c === max).map(([v]) => v).sort((a, b) => a - b);
};

export const sampleVariance = (xs: number[]): number => {
  const m = mean(xs);
  return xs.reduce((acc, x) => acc + (x - m) ** 2, 0) / (xs.length - 1);
};
export const sampleSD = (xs: number[]): number => Math.sqrt(sampleVariance(xs));

export const populationVariance = (xs: number[]): number => {
  const m = mean(xs);
  return xs.reduce((acc, x) => acc + (x - m) ** 2, 0) / xs.length;
};
export const populationSD = (xs: number[]): number => Math.sqrt(populationVariance(xs));

/** Percentile position using the textbook's "k(n+1)/100 = position" locator convention. */
export const quartiles = (xs: number[]): { q1: number; q2: number; q3: number; iqr: number } => {
  const s = [...xs].sort((a, b) => a - b);
  const n = s.length;
  const lower = n % 2 ? s.slice(0, (n - 1) / 2) : s.slice(0, n / 2);
  const upper = n % 2 ? s.slice((n + 1) / 2) : s.slice(n / 2);
  const q1 = median(lower);
  const q3 = median(upper);
  return { q1, q2: median(s), q3, iqr: q3 - q1 };
};

export const round = (x: number, d = 2): number => {
  const f = 10 ** d;
  return Math.round(x * f) / f;
};

export const factorial = (n: number): number => (n <= 1 ? 1 : n * factorial(n - 1));

export const choose = (n: number, k: number): number => {
  if (k < 0 || k > n) return 0;
  let r = 1;
  for (let i = 1; i <= k; i++) r = (r * (n - k + i)) / i;
  return Math.round(r);
};

export const binomialPMF = (n: number, p: number, x: number): number =>
  choose(n, x) * p ** x * (1 - p) ** (n - x);

export const binomialCDF = (n: number, p: number, x: number): number => {
  let s = 0;
  for (let i = 0; i <= x; i++) s += binomialPMF(n, p, i);
  return s;
};

export const geometricPMF = (p: number, x: number): number => (1 - p) ** (x - 1) * p;

export const poissonPMF = (mu: number, x: number): number =>
  (Math.exp(-mu) * mu ** x) / factorial(x);

export const poissonCDF = (mu: number, x: number): number => {
  let s = 0;
  for (let i = 0; i <= x; i++) s += poissonPMF(mu, i);
  return s;
};

export const hypergeometricPMF = (N: number, r: number, n: number, x: number): number =>
  (choose(r, x) * choose(N - r, n - x)) / choose(N, n);

/** Standard normal CDF (Abramowitz & Stegun 26.2.17, |error| < 7.5e-8). */
export const normalCDF = (z: number): number => {
  const t = 1 / (1 + 0.2316419 * Math.abs(z));
  const d = 0.3989422804014327 * Math.exp((-z * z) / 2);
  const p =
    d * t * (0.31938153 + t * (-0.356563782 + t * (1.781477937 + t * (-1.821255978 + t * 1.330274429))));
  return z >= 0 ? 1 - p : p;
};

/** Inverse standard normal CDF (Acklam's algorithm). */
export const normalInv = (p: number): number => {
  if (p <= 0 || p >= 1) throw new Error("p must be in (0,1)");
  const a = [-3.969683028665376e1, 2.209460984245205e2, -2.759285104469687e2, 1.38357751867269e2, -3.066479806614716e1, 2.506628277459239];
  const b = [-5.447609879822406e1, 1.615858368580409e2, -1.556989798598866e2, 6.680131188771972e1, -1.328068155288572e1];
  const c = [-7.784894002430293e-3, -3.223964580411365e-1, -2.400758277161838, -2.549732539343734, 4.374664141464968, 2.938163982698783];
  const d = [7.784695709041462e-3, 3.224671290700398e-1, 2.445134137142996, 3.754408661907416];
  const plow = 0.02425;
  const phigh = 1 - plow;
  let q: number, r: number;
  if (p < plow) {
    q = Math.sqrt(-2 * Math.log(p));
    return (((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
  }
  if (p <= phigh) {
    q = p - 0.5;
    r = q * q;
    return ((((((a[0] * r + a[1]) * r + a[2]) * r + a[3]) * r + a[4]) * r + a[5]) * q) / (((((b[0] * r + b[1]) * r + b[2]) * r + b[3]) * r + b[4]) * r + 1);
  }
  q = Math.sqrt(-2 * Math.log(1 - p));
  return -(((((c[0] * q + c[1]) * q + c[2]) * q + c[3]) * q + c[4]) * q + c[5]) / ((((d[0] * q + d[1]) * q + d[2]) * q + d[3]) * q + 1);
};

/** Log-gamma via Lanczos approximation. */
const logGamma = (x: number): number => {
  const g = 7;
  const coef = [0.99999999999980993, 676.5203681218851, -1259.1392167224028, 771.32342877765313, -176.61502916214059, 12.507343278686905, -0.13857109526572012, 9.9843695780195716e-6, 1.5056327351493116e-7];
  if (x < 0.5) return Math.log(Math.PI / Math.sin(Math.PI * x)) - logGamma(1 - x);
  x -= 1;
  let a = coef[0];
  const t = x + g + 0.5;
  for (let i = 1; i < g + 2; i++) a += coef[i] / (x + i);
  return 0.5 * Math.log(2 * Math.PI) + (x + 0.5) * Math.log(t) - t + Math.log(a);
};

/** Regularized incomplete beta I_x(a,b) via continued fraction (Numerical Recipes). */
const betaInc = (x: number, a: number, b: number): number => {
  if (x <= 0) return 0;
  if (x >= 1) return 1;
  const bt = Math.exp(logGamma(a + b) - logGamma(a) - logGamma(b) + a * Math.log(x) + b * Math.log(1 - x));
  const cf = (x: number, a: number, b: number): number => {
    const MAXIT = 200, EPS = 3e-14, FPMIN = 1e-300;
    const qab = a + b, qap = a + 1, qam = a - 1;
    let c = 1, d = 1 - (qab * x) / qap;
    if (Math.abs(d) < FPMIN) d = FPMIN;
    d = 1 / d;
    let h = d;
    for (let m = 1; m <= MAXIT; m++) {
      const m2 = 2 * m;
      let aa = (m * (b - m) * x) / ((qam + m2) * (a + m2));
      d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN;
      c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN;
      d = 1 / d; h *= d * c;
      aa = (-(a + m) * (qab + m) * x) / ((a + m2) * (qap + m2));
      d = 1 + aa * d; if (Math.abs(d) < FPMIN) d = FPMIN;
      c = 1 + aa / c; if (Math.abs(c) < FPMIN) c = FPMIN;
      d = 1 / d;
      const del = d * c;
      h *= del;
      if (Math.abs(del - 1) < EPS) break;
    }
    return h;
  };
  return x < (a + 1) / (a + b + 2) ? (bt * cf(x, a, b)) / a : 1 - (bt * cf(1 - x, b, a)) / b;
};

/** Student t CDF. */
export const tCDF = (t: number, df: number): number => {
  const x = df / (df + t * t);
  const p = 0.5 * betaInc(x, df / 2, 0.5);
  return t >= 0 ? 1 - p : p;
};

/** Inverse t CDF by bisection (sufficient for tables/critical values). */
export const tInv = (p: number, df: number): number => {
  let lo = -50, hi = 50;
  for (let i = 0; i < 200; i++) {
    const mid = (lo + hi) / 2;
    if (tCDF(mid, df) < p) lo = mid; else hi = mid;
  }
  return (lo + hi) / 2;
};

/** Regularized lower incomplete gamma P(a, x) (series / continued fraction). */
const gammaP = (a: number, x: number): number => {
  if (x <= 0) return 0;
  if (x < a + 1) {
    let sum = 1 / a, del = sum, ap = a;
    for (let n = 0; n < 500; n++) {
      ap += 1; del *= x / ap; sum += del;
      if (Math.abs(del) < Math.abs(sum) * 3e-14) break;
    }
    return sum * Math.exp(-x + a * Math.log(x) - logGamma(a));
  }
  let b = x + 1 - a, c = 1 / 1e-300, d = 1 / b, h = d;
  for (let i = 1; i < 500; i++) {
    const an = -i * (i - a);
    b += 2;
    d = an * d + b; if (Math.abs(d) < 1e-300) d = 1e-300;
    c = b + an / c; if (Math.abs(c) < 1e-300) c = 1e-300;
    d = 1 / d;
    const del = d * c;
    h *= del;
    if (Math.abs(del - 1) < 3e-14) break;
  }
  return 1 - Math.exp(-x + a * Math.log(x) - logGamma(a)) * h;
};

/** Chi-square CDF. */
export const chiSquareCDF = (x: number, df: number): number => gammaP(df / 2, x / 2);

export const chiSquareInv = (p: number, df: number): number => {
  let lo = 0, hi = Math.max(10, df * 10);
  for (let i = 0; i < 200; i++) {
    const mid = (lo + hi) / 2;
    if (chiSquareCDF(mid, df) < p) lo = mid; else hi = mid;
  }
  return (lo + hi) / 2;
};

/** F distribution CDF. */
export const fCDF = (f: number, df1: number, df2: number): number => {
  if (f <= 0) return 0;
  return betaInc((df1 * f) / (df1 * f + df2), df1 / 2, df2 / 2);
};

export const fInv = (p: number, df1: number, df2: number): number => {
  let lo = 0, hi = 1000;
  for (let i = 0; i < 200; i++) {
    const mid = (lo + hi) / 2;
    if (fCDF(mid, df1, df2) < p) lo = mid; else hi = mid;
  }
  return (lo + hi) / 2;
};

export const exponentialCDF = (x: number, m: number): number => (x < 0 ? 0 : 1 - Math.exp(-m * x));

/** Pearson correlation coefficient. */
export const correlation = (xs: number[], ys: number[]): number => {
  const mx = mean(xs), my = mean(ys);
  let sxy = 0, sxx = 0, syy = 0;
  for (let i = 0; i < xs.length; i++) {
    sxy += (xs[i] - mx) * (ys[i] - my);
    sxx += (xs[i] - mx) ** 2;
    syy += (ys[i] - my) ** 2;
  }
  return sxy / Math.sqrt(sxx * syy);
};

/** Least-squares line ŷ = a + bx. */
export const regression = (xs: number[], ys: number[]): { a: number; b: number; r: number } => {
  const mx = mean(xs), my = mean(ys);
  let sxy = 0, sxx = 0;
  for (let i = 0; i < xs.length; i++) {
    sxy += (xs[i] - mx) * (ys[i] - my);
    sxx += (xs[i] - mx) ** 2;
  }
  const b = sxy / sxx;
  return { a: my - b * mx, b, r: correlation(xs, ys) };
};

export const fmt = (x: number, d = 2): string => {
  const r = round(x, d);
  return Number.isInteger(r) ? String(r) : r.toFixed(d).replace(/0+$/, "").replace(/\.$/, "");
};
