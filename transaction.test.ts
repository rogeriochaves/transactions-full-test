import * as sqlite3 from "better-sqlite3";
import * as transaction from "./transaction";
import fc from "fast-check";
// const fc = require('fast-check');

// const contains = (text, pattern) => text.indexOf(pattern) >= 0;

describe("transferMoney", () => {
  let db : sqlite3.Database;

  beforeEach(() => {
    db = sqlite3(':memory:');
    db.exec("CREATE TABLE balance (account TEXT, amount INT)");
    db.exec("INSERT INTO balance(account, amount) VALUES ('Alice', 10)");
    db.exec("INSERT INTO balance(account, amount) VALUES ('Bob', 5)");
  });

  it("transfers money from Alice to Bob", () => {
    transaction.transferMoney(db, { from: 'Alice', to: 'Bob', amount: 10 });
    const alice = db.prepare("SELECT amount FROM balance WHERE account = 'Alice'").get();
    expect(alice.amount).toBe(0);

    const bob = db.prepare("SELECT amount FROM balance WHERE account = 'Bob'").get();
    expect(bob.amount).toBe(15);
  });

  it('ends up with more money on the receiving account', () => {
    fc.assert(fc.property(fc.integer(), amount => {
      db.prepare("UPDATE balance SET amount = 10").run();

      try {
        transaction.transferMoney(db, { from: 'Alice', to: 'Bob', amount });
      } catch (_) { return; }

      const alice = db.prepare("SELECT amount FROM balance WHERE account = 'Alice'").get();
      expect(alice.amount).toBeGreaterThanOrEqual(0);
      const bob = db.prepare("SELECT amount FROM balance WHERE account = 'Bob'").get();
      expect(bob.amount).toBeGreaterThan(alice.amount);
    }));
  });
});
