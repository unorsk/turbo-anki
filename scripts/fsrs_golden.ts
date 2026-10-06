// Golden vectors for TurboAnkiTests.Fsrs: runs melk's FSRS on fixed review sequences.
// Usage: node scripts/fsrs_golden.ts ../melk2/server/src/fsrs.ts
const { fsrsNext, NEW_CARD } = await import(process.argv[2]);

const DAY = 86_400_000;
const MIN = 60_000;
const start = Date.UTC(2026, 0, 1);
// Each sequence: [minutes after the previous review, rating]...
const sequences: [number, number][][] = [
  [[0, 3], [10, 3], [60 * 24 * 3, 3], [60 * 24 * 10, 3], [60 * 24 * 30, 3]],
  [[0, 1], [1, 1], [5, 2], [10, 3], [60 * 24 * 2, 1], [5, 3], [60 * 24 * 1, 4]],
  [[0, 4], [60 * 24 * 20, 2], [60 * 24 * 5, 3], [60 * 24 * 40, 4]],
  [[0, 2], [5, 3], [60 * 24 * 7, 1], [5, 1], [5, 2], [10, 3], [60 * 24 * 365, 3]],
];
for (const seq of sequences) {
  let card = NEW_CARD;
  let t = start;
  const out: string[] = [];
  for (const [mins, rating] of seq) {
    t += mins * MIN;
    const r = fsrsNext(card, new Date(t), rating);
    card = r.card;
    out.push(
      `(${card.state}, ${Date.parse(card.due) - t}, ${card.stability.toFixed(6)}, ` +
        `${card.difficulty.toFixed(6)}, ${card.elapsedDays}, ${card.scheduledDays}, ${card.reps}, ${card.lapses})`,
    );
  }
  console.log(`[${out.join(",\n   ")}]`);
}
