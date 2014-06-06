public class output {

    // data nat where
    //  zero : nat
    //  suc : nat -> nat
    public static abstract class nat {
	public static int zero_TAG = 0;
	public static int suc_TAG = 1;
	public abstract int getTag();
    }

    public static class zero extends nat {
	public int getTag() {
	    return zero_TAG;
	}
	public zero() {}
	public String toString() {
	    return "zero";
	}
    }

    public static class suc extends nat {
	public int getTag() {
	    return suc_TAG;
	}
	protected nat suc_data0;
	public suc(nat suc_data0) {
	    this.suc_data0 = suc_data0;
	}
	public nat get_suc_data0() {
	    return suc_data0;
	}

	public String toString() {
	    return "(suc " + (suc_data0.toString()) + ")";
	}
    }

    // fun add : nat -> nat -> nat
    // add zero y = y .
    // add (suc x) y = suc (add x y) .
    public static nat add(nat x0, nat x1) {
	if (x0.getTag() == nat.zero_TAG) {
	    nat y = x1;
	    
	    return y;
	}

	if (x0.getTag() == nat.suc_TAG) {
	    nat x = ((suc)x0).get_suc_data0();
	    nat y = x1;
	    
	    return new suc(add(x,y));
	}
	
	return null;
    }

    public static void main(String[] args) {

	// fun main : nat
        // main = add (suc zero) (suc zero) .
	nat main = add(new suc(new zero()),new suc(new zero()));

	System.out.println(main.toString());
    }
}