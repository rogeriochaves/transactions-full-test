import * as sqlite3 from 'better-sqlite3';
import * as transaction from "./transaction";

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

  // it("sending undefined does not transfer any amount", () => {
  //   transaction.transferMoney(db, { from: 'Alice', to: 'Bob', amount: undefined });

  //   const alice = db.get("SELECT amount FROM balance WHERE account = 'Alice'");
  //   expect(alice.amount).toBe(10);

  //   const bob = db.get("SELECT amount FROM balance WHERE account = 'Bob'");
  //   expect(bob.amount).toBe(15);
  // });

  // it('should always contain itself', () => {
  //   fc.assert(fc.property(fc.number(), text => contains(text, text)));
  // });
});
