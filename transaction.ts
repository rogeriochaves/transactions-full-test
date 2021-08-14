import { Database } from "better-sqlite3";

export function transferMoney(
    db: Database,
    { from, to, amount }: { from: string, to: string, amount: number }
) {
    if (amount <= 0) throw "only positive amounts are allowed to be transferred";

    const balance_from = db.prepare("SELECT amount FROM balance WHERE account = ?").get(from);
    if (amount > balance_from.amount) throw "there is not enough money to be transferred";

    db.prepare("UPDATE balance SET amount = amount - ? WHERE account = ?").run(amount, from);
    db.prepare("UPDATE balance SET amount = amount + ? WHERE account = ?").run(amount, to);
}
