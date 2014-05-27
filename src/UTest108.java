public class UTest108 {
  public static void l() {
    MissileBattery r = new MissileBattery(4);
    int i = 5;
    while(i > 2)
    {
    	i--;
    	if (i > 0)
    		break;
    	else
    		r.fire(i);
    }
    r.fire(i);
    
    
    
  }
}