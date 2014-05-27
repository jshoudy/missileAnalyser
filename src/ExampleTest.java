public class ExampleTest {
	public static void l() {
		
		MissileBattery a = new MissileBattery(30);
		MissileBattery b = a;
		int i = 27;
		int j = 4;
		while (i < 40) {
			i++;
			if (j == 5)
				i --;
		}

		b.fire(i);
		
	  }
}
 

