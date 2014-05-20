public class ExampleTest {
  public static void l(){
	MissileBattery b = new MissileBattery(50);
	
	int i = 15;
	int j = 10;
	if(i > 10 && i < 20){
		b.fire(i);
	}
  }
  

  public static void b(){
	MissileBattery b = new MissileBattery(50);
	
	int i = 15;
	int j = 10;
	if(i > 10 && i < 20){
		b.fire(i+1-1);
		b.fire(i);
	}
  }
}

