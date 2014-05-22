public class ExampleTest {
	public static void l() {
		
		
		MissileBattery r = new MissileBattery(10);
	    int i = 2;
	    int j = 8;
	    while (i < 5) {
	    	i = i+1;
	    }
	    r.fire(i);
	    if (i==3) {
			r.fire(j);
		}
	    MissileBattery m = new MissileBattery(6);
	    while (i >=2) {
	    	i = i + 1;
	    }
	    m.fire(i);
		
		
		
	  }
}
 

