/**
 * Reset Axioms (Constellation v0.14.0 §9) — load-bearing for this module.
 *
 *   A1  Ephemeroi is not a belief system. It constructs provisional world
 *       models from observations, constraints, mechanisms, and predictive
 *       testing.
 *   A2  All abstractions are tools, not truths. Speculation must be
 *       labeled. Confidence must be earned.
 *   A3  Mechanisms outrank metaphor. A beautiful theory that predicts
 *       nothing is decoration.
 *   A4  Prediction outranks elegance. Reality outranks narrative.
 *   A5  Fresh evidence outranks memory. Reality Layer recomputes from
 *       scratch every cycle. No trust value overrides raw clause
 *       satisfaction.
 *   A6  The squirrel problem propagates. Any system that accumulates
 *       orientation-like state is a squirrel attack surface; apply
 *       adversarial probing at every accumulation point.
 *
 * This module is the first place A2-A4 are enforced in the TS solver:
 * every escape mechanism enters as `speculative`, is forced to make a
 * prediction at firing time, and only earns `mechanism` status by
 * surviving contact with the unsat trajectory (the Reality Layer).
 * Failures demote. Stale confidence does not survive.
 *
 * HypothesisLedger
 * ----------------
 * Tracks every "escape mechanism" firing (AdversarialRestart, Cyrus Edict)
 * as a labelled hypothesis with an explicit prediction, then evaluates
 * whether the prediction survived contact with reality (unsat trajectory).
 *
 * This is the v0.14.0 Constellation doc's HIGH-priority gap #2 — multi-cycle
 * confidence tracking — applied at the mechanism level instead of the
 * variable level. The Reality Layer here is the unsat count: a hypothesis
 * predicts that unsat will drop by at least `minDeltaUnsat` within
 * `windowSteps` of firing, and the ledger records survived/failed against
 * that prediction.
 *
 * Per-mechanism aggregate status follows the doc:
 *   speculative -> mechanism  after 3 consecutive survivals
 *   speculative -> demoted    after 2 consecutive failures
 *   demoted     -> speculative on the next survival
 *   mechanism   -> speculative on the next failure
 *
 * The ledger is a process-wide singleton. It does not persist to the DB —
 * it is a live diagnostic surface read via GET /ephemeroi/hypothesis-ledger.
 */

export type EscapeMechanism = "AdversarialRestart" | "CyrusEdict";

export type HypothesisStatus = "pending" | "survived" | "failed";

export type MechanismConfidence = "speculative" | "demoted" | "mechanism";

export interface HypothesisPrediction {
  /** Window in solver steps within which the prediction must hold. */
  windowSteps: number;
  /** Minimum unsat reduction required for the hypothesis to survive. */
  minDeltaUnsat: number;
}

export interface Hypothesis {
  id: number;
  mechanism: EscapeMechanism;
  /** Solver run that fired the hypothesis — used to scope tick(). */
  runId: string;
  registeredAtStep: number;
  unsatBefore: number;
  prediction: HypothesisPrediction;
  status: HypothesisStatus;
  /** Step at which the prediction was resolved. Null while pending. */
  resolvedAtStep: number | null;
  /** Unsat at resolution. Null while pending. */
  unsatAtResolution: number | null;
  /** Brief human-readable note populated when resolved. */
  outcomeNote: string | null;
}

export interface MechanismStats {
  mechanism: EscapeMechanism;
  totalFired: number;
  totalSurvived: number;
  totalFailed: number;
  consecutiveSurvivals: number;
  consecutiveFailures: number;
  confidence: MechanismConfidence;
}

export interface LedgerSnapshot {
  hypotheses: Hypothesis[];
  stats: MechanismStats[];
  generatedAt: string;
}

const DEFAULT_PREDICTIONS: Record<EscapeMechanism, HypothesisPrediction> = {
  // Adversarial restart force-flips the consensus heavies; it should
  // visibly punch unsat down within ~30 steps or it failed to break the
  // basin we suspected.
  AdversarialRestart: { windowSteps: 30, minDeltaUnsat: 1 },
  // Cyrus Edict is a faster surgical move on a cage — narrower window.
  CyrusEdict: { windowSteps: 10, minDeltaUnsat: 1 },
};

const SURVIVAL_PROMOTION_THRESHOLD = 3;
const FAILURE_DEMOTION_THRESHOLD = 2;

export class HypothesisLedger {
  private hypotheses: Hypothesis[] = [];
  private statsByMechanism = new Map<EscapeMechanism, MechanismStats>();
  private nextId = 1;
  /** Cap on retained hypotheses to keep the snapshot bounded. */
  private readonly maxRetained: number;

  constructor(opts: { maxRetained?: number } = {}) {
    this.maxRetained = Math.max(50, opts.maxRetained ?? 500);
  }

  /**
   * Record a new hypothesis when an escape mechanism fires. Returns the
   * hypothesis id so the caller can correlate logs.
   */
  register(args: {
    mechanism: EscapeMechanism;
    runId: string;
    step: number;
    unsatBefore: number;
    prediction?: Partial<HypothesisPrediction>;
  }): Hypothesis {
    const base = DEFAULT_PREDICTIONS[args.mechanism];
    const prediction: HypothesisPrediction = {
      windowSteps: args.prediction?.windowSteps ?? base.windowSteps,
      minDeltaUnsat: args.prediction?.minDeltaUnsat ?? base.minDeltaUnsat,
    };
    const h: Hypothesis = {
      id: this.nextId++,
      mechanism: args.mechanism,
      runId: args.runId,
      registeredAtStep: args.step,
      unsatBefore: args.unsatBefore,
      prediction,
      status: "pending",
      resolvedAtStep: null,
      unsatAtResolution: null,
      outcomeNote: null,
    };
    this.hypotheses.push(h);
    this.bumpFiredCount(args.mechanism);
    this.evictIfOverCap();
    return h;
  }

  /**
   * Called once per solver step with the current run's unsat. Resolves
   * any pending hypotheses for this run whose window has either closed
   * or whose unsat reduction target has already been met.
   */
  tick(args: { runId: string; step: number; unsat: number }): void {
    for (const h of this.hypotheses) {
      if (h.status !== "pending") continue;
      if (h.runId !== args.runId) continue;
      const elapsed = args.step - h.registeredAtStep;
      const delta = h.unsatBefore - args.unsat;
      const targetMet = delta >= h.prediction.minDeltaUnsat;
      const windowClosed = elapsed >= h.prediction.windowSteps;
      if (targetMet) {
        this.resolve(h, args.step, args.unsat, "survived",
          `unsat fell ${delta} within ${elapsed} steps (target ${h.prediction.minDeltaUnsat} within ${h.prediction.windowSteps})`);
      } else if (windowClosed) {
        this.resolve(h, args.step, args.unsat, "failed",
          `unsat moved ${delta} in ${elapsed} steps (target ${h.prediction.minDeltaUnsat} within ${h.prediction.windowSteps})`);
      }
    }
  }

  /**
   * Force-fail any hypotheses still pending for a run that has ended.
   * Called by the biomimetic runner when the loop exits, so we don't
   * leave pending entries dangling forever.
   */
  finalizeRun(args: { runId: string; finalStep: number; finalUnsat: number }): void {
    for (const h of this.hypotheses) {
      if (h.status !== "pending") continue;
      if (h.runId !== args.runId) continue;
      const delta = h.unsatBefore - args.finalUnsat;
      if (delta >= h.prediction.minDeltaUnsat) {
        this.resolve(h, args.finalStep, args.finalUnsat, "survived",
          `run ended; unsat fell ${delta} cumulatively (target ${h.prediction.minDeltaUnsat})`);
      } else {
        this.resolve(h, args.finalStep, args.finalUnsat, "failed",
          `run ended at step ${args.finalStep}; unsat moved ${delta} (target ${h.prediction.minDeltaUnsat})`);
      }
    }
  }

  snapshot(): LedgerSnapshot {
    return {
      hypotheses: this.hypotheses.map((h) => ({ ...h })),
      stats: Array.from(this.statsByMechanism.values()).map((s) => ({ ...s })),
      generatedAt: new Date().toISOString(),
    };
  }

  /** Test-only. Wipes everything. */
  reset(): void {
    this.hypotheses = [];
    this.statsByMechanism.clear();
    this.nextId = 1;
  }

  private resolve(
    h: Hypothesis,
    step: number,
    unsat: number,
    status: "survived" | "failed",
    note: string,
  ): void {
    h.status = status;
    h.resolvedAtStep = step;
    h.unsatAtResolution = unsat;
    h.outcomeNote = note;
    const stats = this.ensureStats(h.mechanism);
    if (status === "survived") {
      stats.totalSurvived += 1;
      stats.consecutiveSurvivals += 1;
      stats.consecutiveFailures = 0;
      if (stats.confidence === "demoted") {
        stats.confidence = "speculative";
      } else if (
        stats.confidence === "speculative" &&
        stats.consecutiveSurvivals >= SURVIVAL_PROMOTION_THRESHOLD
      ) {
        stats.confidence = "mechanism";
      }
    } else {
      stats.totalFailed += 1;
      stats.consecutiveFailures += 1;
      stats.consecutiveSurvivals = 0;
      if (stats.confidence === "mechanism") {
        stats.confidence = "speculative";
      } else if (
        stats.confidence === "speculative" &&
        stats.consecutiveFailures >= FAILURE_DEMOTION_THRESHOLD
      ) {
        stats.confidence = "demoted";
      }
    }
  }

  private ensureStats(m: EscapeMechanism): MechanismStats {
    let s = this.statsByMechanism.get(m);
    if (!s) {
      s = {
        mechanism: m,
        totalFired: 0,
        totalSurvived: 0,
        totalFailed: 0,
        consecutiveSurvivals: 0,
        consecutiveFailures: 0,
        confidence: "speculative",
      };
      this.statsByMechanism.set(m, s);
    }
    return s;
  }

  private bumpFiredCount(m: EscapeMechanism): void {
    this.ensureStats(m).totalFired += 1;
  }

  private evictIfOverCap(): void {
    if (this.hypotheses.length <= this.maxRetained) return;
    // Drop oldest resolved entries first; never drop pending ones.
    const overflow = this.hypotheses.length - this.maxRetained;
    let dropped = 0;
    this.hypotheses = this.hypotheses.filter((h) => {
      if (dropped >= overflow) return true;
      if (h.status === "pending") return true;
      dropped += 1;
      return false;
    });
  }
}

/** Process-wide singleton. */
export const hypothesisLedger = new HypothesisLedger();
