//
//  UserDefaults.h
//  Mariani
//
//  Created by Steven Huang on 1/2/22.
//

#import <Foundation/Foundation.h>

NS_ASSUME_NONNULL_BEGIN

@interface UserDefaults : NSObject

+ (instancetype)sharedInstance;

@property (nonatomic) NSURL *screenshotsFolder;

@end

NS_ASSUME_NONNULL_END