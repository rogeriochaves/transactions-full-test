import { Database } from 'better-sqlite3';

export function transferMoney(
    db: Database,
    { from, to, amount }: { from: string, to: string, amount: number }
) {
    const balance_from = db.prepare("SELECT amount FROM balance WHERE account = ?").get(from);
    const balance_to = db.prepare("SELECT amount FROM balance WHERE account = ?").get(to);

    db.prepare("UPDATE balance SET amount = ? WHERE account = ?").run(balance_from.amount - amount, from);
    db.prepare("UPDATE balance SET amount = ? WHERE account = ?").run(balance_to.amount + amount, to);
}
