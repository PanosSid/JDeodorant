package replace_typecode_with_subclass;
import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.nio.file.StandardCopyOption;

public class FileUtils {
	
	public static void restoreOriginalFile(String originalFilePath, String targetDirectory) {
//    	System.out.println(originalFilePath);
//    	System.out.println(targetDirectory);
        try {
            Path source = Paths.get(originalFilePath);
            Path destination = Paths.get(targetDirectory);

            if (!Files.isDirectory(destination)) {
//                System.err.println("The target path is not a directory.");
                return;
            }

            Files.copy(source, destination.resolve(source.getFileName()), StandardCopyOption.REPLACE_EXISTING);
//            System.out.println("File restored successfully!");
        } catch (IOException e) {
            e.printStackTrace();
        }
    }

	public static void deleteFilesInDirectory(String directoryPath) {
//    	System.out.println(directoryPath);
		File directory = new File(directoryPath);

		if (directory.exists() && directory.isDirectory()) {
			File[] files = directory.listFiles();
			if (files != null) {
				for (File file : files) {
					if (file.isFile()) {
						file.delete();
					}
				}
			}
		}
	}

	
}
