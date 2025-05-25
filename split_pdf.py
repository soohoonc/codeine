# import fitz  # PyMuPDF
# import io
# from PIL import Image
# import os
# def extract_images_from_pdf(pdf_path, output_folder):
#     pdf_document = fitz.open(pdf_path)
#     if not os.path.exists(output_folder):
#         os.makedirs(output_folder)
#     for page_num in range(len(pdf_document)):
#         page = pdf_document.load_page(page_num)
#         image_list = page.get_images()
        
#         for img_index, img in enumerate(image_list):
#             xref = img[0]
#             pix = fitz.Pixmap(pdf_document, xref)
            
#             if pix.n - pix.alpha < 4:  # GRAY or RGB
#                 img_data = pix.tobytes("png")
#                 img_name = f"{page_num + 1:04d}.png"
                
#                 with open(f"{output_folder}/{img_name}", "wb") as img_file:
#                     img_file.write(img_data)
            
#             pix = None
    
#     pdf_document.close()

# extract_images_from_pdf("data/whiteheadrussell-principiamathematicavolumei.pdf", "data/principia")