/**
 * 
 */
package lu.uni.lassy.metrics;

import java.util.logging.Handler;
import java.util.logging.LogRecord;

/**
 * @author gperroui
 *
 */
public class LogHandler extends Handler {

	/* (non-Javadoc)
	 * @see java.util.logging.Handler#close()
	 */
	@Override
	public void close() throws SecurityException {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.util.logging.Handler#flush()
	 */
	@Override
	public void flush() {
		// TODO Auto-generated method stub

	}

	/* (non-Javadoc)
	 * @see java.util.logging.Handler#publish(java.util.logging.LogRecord)
	 */
	@Override
	public void publish(LogRecord arg0) {
		// TODO Auto-generated method stub
		//System.out.println("Logger : " + arg0.getLoggerName() + " : " + arg0.getMessage());	
	}

}
