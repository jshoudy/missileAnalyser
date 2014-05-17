public class ExampleTest {
  public static void l(){
	MissileBattery b = new MissileBattery(2);
	b.fire(1);
  }
  public static void IF_TESTER() {
	int i = 20;
	int ii = 20;
	MissileBattery b = new MissileBattery(2);
	
	int ten = 10;
	// NEQ
	if(20 != i){
		b.fire(i);
	}
	if(ii != i){
		b.fire(i);
	}
	if(i != 20){
		b.fire(i);
	}
	
	// LE  
	if(i < 10){
		b.fire(i);
	}
	if(i < ten){
		b.fire(i);
	}
	if(10 < i){
	}else{
		b.fire(i);
	}
	
	// LEQ
	if(i <= 10){
		b.fire(i);
	}
	if(i <= ten){
		b.fire(i);
	}
	if(10 <= i){
	}else{
		b.fire(i);
	}
	
	// EQ
	if(i == 9){
		b.fire(i);
	}
	if(i == ten){
		b.fire(i);
	}
	if(9 == i){
		b.fire(i); 
	}

	//GE
	if(10 > i){
		b.fire(i);
	}
	if(ten > i){
		b.fire(i);
	}
	if(i > 30){
		b.fire(i);
	}

	//GEQ
	if(10 >= i){
		b.fire(i);
	}
	if(ten >= i){
		b.fire(i);
	}
	if(i >= 30){
		b.fire(i);
	}

	b.fire(1);
	
  }
}

