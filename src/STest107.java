public class STest107 {
  public static void l() {
    MissileBattery r = new MissileBattery(6);
    MissileBattery s = new MissileBattery(6);
    MissileBattery q = s;
    int i = -10;
    int j;
    if(i > 0)
    	j = -3;
    else
    {
    	j = 2;
    }
    q.fire(j);
    r.fire(j);
    
    
  }
}