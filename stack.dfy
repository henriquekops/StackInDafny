class {:autocontracts} Stack
{
    // Abstraction
    ghost const MAXSIZE: nat;
    ghost var content: seq<int>;

    // Implementation
    var a: array<int>;
    var cursor: nat;
    const max: nat;

    // Class invariant
    predicate Valid()
    {
        max > 0
        && a.Length == max
        && 0 <= cursor <= max
        && MAXSIZE == max
        && content == a[0..cursor]
    }
    
    // Constructor for this class
    constructor (s: nat)
    requires s > 0
    ensures s == MAXSIZE
    ensures content == []
    ensures cursor == 0
    {
        MAXSIZE := s;
        max := s;
        a := new int[s];
        cursor := 0;
        content := [];
    }

    // Add item in this stack
    method add(e:int) returns (b: bool)
    ensures b ==> content == old(content) + [e]
    ensures !b ==> content == old(content)
    ensures b <==> |old(content)| < MAXSIZE
    {
        var full := isFull();
        if full {
            b := false;
        } else {
            a[cursor] := e;
            cursor := cursor + 1;
            content := content + [e];
            b := true;
        }
    }

    // Pop an item from this stack
    method pop() returns (e: int)
    requires |content| > 0
    ensures e == old(content)[|old(content)| - 1]
    ensures content == old(content)[0..|old(content)| - 1]
    {
        e := a[cursor - 1];
        cursor := cursor - 1;
        content := a[..cursor];
    }

    // Peeks an item from this stack
    method peek() returns (e: int)
    requires |content| > 0
    ensures content == old(content)
    ensures e == content[|content| - 1]
    {
        e := a[cursor-1];
    }

    // Checks if this stack is full
    method isFull() returns (b: bool)
    ensures content == old(content)
    ensures b <==> |content| == MAXSIZE
    {
        b := cursor == max;
    }

    // Checks if this stack is empty
    method isEmpty() returns (b: bool)
    ensures content == old(content)
    ensures b <==> |content| == 0
    {
        b := cursor == 0;
    }
    
    // Checks how many items this stack contains
    method howMany() returns (m: nat)
    ensures content == old(content)
    ensures m == |content|
    {
        m := cursor;
    }

    // Gets the maximum size of this stack
    method maxSize() returns (m: nat)
    ensures content == old(content)
    ensures m == MAXSIZE
    {
        m := max;
    }

    // Inverts this stack
    method invert()
    requires |content| > 0
    ensures |content| == |old(content)|
    ensures forall i | 0 <= i < |content| :: content[i] == old(content[|content| - i - 1])
    {
        var b := new int[max];

        forall i | 0 <= i < cursor
        {
            b[i] := a[cursor - i - 1];
        }

        a := b;
        content := a[..cursor];
    }

    // Shows this stack content
    method show()
    ensures old(content) == content
    {
        print(a[..cursor]);
        print("\n");
    }

}

method Main()
{
    // Stack creation
    var stack := new Stack(5);

    var isEmpty := stack.isEmpty();
    assert isEmpty;
    var isFull := stack.isFull();
    assert !isFull;
    var howMany := stack.howMany();
    assert howMany == 0;

    stack.show();

    // Stack addition
    var a := stack.add(1);
    assert a;
    var b := stack.add(2);
    assert b;
    var c := stack.add(3);
    assert c;

    howMany := stack.howMany();
    assert howMany == 3;
    var maxSize := stack.maxSize();
    assert maxSize == 5;
    var peek := stack.peek();
    assert peek == 3;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    isFull := stack.isFull();
    assert !isFull;

    stack.show();

    // Stack addition until is full
    var d := stack.add(4);
    assert d;
    var e := stack.add(5);
    assert e;
    var f := stack.add(6);
    assert !f;

    peek := stack.peek();
    assert peek == 5;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    isFull := stack.isFull();
    assert isFull;
    howMany := stack.howMany();
    assert howMany == 5;

    stack.show();

    // Stack popping
    var pop := stack.pop();
    assert pop == 5;

    isFull := stack.isFull();
    assert !isFull;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    howMany := stack.howMany();
    assert howMany == 4;
    peek := stack.peek();
    assert peek == 4;

    stack.show();

    // Stack invertion
    stack.invert();

    isFull := stack.isFull();
    assert !isFull;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    howMany := stack.howMany();
    assert howMany == 4;
    peek := stack.peek();
    assert peek == 1;

    stack.show();

    // Stack popping after inversion
    pop := stack.pop();
    assert pop == 1;

    isFull := stack.isFull();
    assert !isFull;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    howMany := stack.howMany();
    assert howMany == 3;
    maxSize := stack.maxSize();
    assert maxSize == 5;
    peek := stack.peek();
    assert peek == 2;

    stack.show();

    // Stack addition after inversion
    var g := stack.add(7);
    assert g;

    isFull := stack.isFull();
    assert !isFull;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    howMany := stack.howMany();
    assert howMany == 4;
    maxSize := stack.maxSize();
    assert maxSize == 5;
    peek := stack.peek();
    assert peek == 7;

    stack.show();
    
    // Stack addition until is full after inversion
    var h := stack.add(8);
    assert h;

    isFull := stack.isFull();
    assert isFull;
    isEmpty := stack.isEmpty();
    assert !isEmpty;
    howMany := stack.howMany();
    assert howMany == 5;
    maxSize := stack.maxSize();
    assert maxSize == 5;
    peek := stack.peek();
    assert peek == 8;

    stack.show();
}
